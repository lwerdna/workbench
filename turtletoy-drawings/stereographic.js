// created by Andrew Lamoureux (andrewl) - 2019
// License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

const nlats = 32
const nlongs = 64
const nverts = 1 + nlats*nlongs + 1
const radius = 90

Canvas.setpenopacity(.1);
const turtle = new Turtle();

/* get, rotate the sphere */
vertices = []
polyidxs = []
gen_sphere()
for(i=0; i<vertices.length; ++i) {
    var [x,y,z] = vertices[i]
    var [x,y,z] = rotx(x,y,z,.3)
    var [x,y,z] = roty(x,y,z,1.2)
    vertices[i] = [x,y,z]
}
    
/* convert all 3d sphere points to 2d plane points
    (this is the stereographic projection) */
points2d = []
for(i=0; i<vertices.length; ++i) {
    var [x,y,z] = vertices[i]
    if(z == 1) {
        points2d.push(null)
        continue
    }
    x_ = (.41*radius)* x/(radius-z)
    y_ = (.41*radius)* y/(radius-z)
    points2d.push([x_,y_])
}

function walk(fan)
{
    fills = [1,8]
    /* draw one "fan" of blade polygons */
    for(blade=0; blade<nlongs; ++blade) {
        i = fan*nlongs + blade
	    poly = []
        for(j=0; j<polyidxs[i].length; ++j)
	        poly.push(points2d[polyidxs[i][j]])

        if(inbounds(poly))
	        polyfill(poly, fills[(fan+blade)%2])
    }

    return fan<nlats
}

//------------------------------------------------------------------------------
// 3d rotations
//------------------------------------------------------------------------------

function rotx(x,y,z, angle)
{
	s = Math.sin(angle)
	c = Math.cos(angle)
	return [x, c*y-s*z, s*y+c*z]
}

function roty(x,y,z, angle)
{
	s = Math.sin(angle)
	c = Math.cos(angle)
	return [c*x+s*z, y, -s*x+c*z]
}

function rotz(x,y,z, angle)
{
	s = Math.sin(angle)
	c = Math.cos(angle)
	return [c*x-s*y, s*x+c*y, z]
}

//------------------------------------------------------------------------------
// 3d object
//------------------------------------------------------------------------------

function gen_sphere()
{
	anglediv = Math.PI/(nlats + 1)
	// south pole
	vertices.push([0,-radius,0])
	// latitudes/longitudes
	for(anglestep=1; anglestep<(nlats+1); ++anglestep) {
		angle = 3*Math.PI/2 + (anglestep*anglediv)
		x = radius*Math.cos(angle)
		y = radius*Math.sin(angle)
		z = 0
		// rotate about y
		for(si=0; si<nlongs; ++si) {
            spin = si/nlongs*2*Math.PI
			var [x2,y2,z2] = roty(x,y,z, spin)
			vertices.push([x2,y2,z2])
		}
	}
	// north pole
	vertices.push([0,radius,0])
	
    // build all the polygons
    for(i=0; i<nlongs; ++i)
        polyidxs.push([0,i+1,(i+1)%nlongs + 1])
    for(lat=0; lat<nlats-1; ++lat) {
        base = 1+lat*nlongs
        for(idx=0; idx<nlongs; ++idx) {
            polyidxs.push(
                [base+idx, base+(idx+1)%nlongs,
                base+(idx+1)%nlongs+nlongs, base+idx+nlongs])
        }
    }
    base = nverts-1-nlongs
    for(idx=0; idx<nlongs; ++idx)
        polyidxs.push([base+idx, base+(idx+1)%nlongs, nverts-1])
}

//------------------------------------------------------------------------------
// etc.
//------------------------------------------------------------------------------

function line(x0,y0,x1,y1)
{
    //console.log('line('+x0+','+y0+','+x1+','+y1+')')
    turtle.penup()
    turtle.goto(x0,y0)
    turtle.pendown()
    turtle.goto(x1,y1)
}

function dot(x,y)
{
    //console.log('dot('+x0+','+y0+','+x1+','+y1+')')
    turtle.penup()
    turtle.goto(x,y)
    turtle.pendown()
    turtle.goto(x+1,y)
    turtle.goto(x+1,y+1)
    turtle.goto(x,y+1)
    turtle.goto(x,y)
}

function inbounds(poly)
{
    for(i=0; i<poly.length; ++i) {
        var [x,y] = [poly[i][0], poly[i][1]]
        if(x>=-100 && x<=100 && y>=-100 && y<=100)
            return true
    }
    
    return false
}

/* scan-line polygon fill
    WARNNG: basic implementation, no optimizations here */
function polyfill(points, lrepeat)
{
	lines = []
    scan_start = 100
    scan_end = -100

	for(i=0; i<points.length; i++) {            /* collect lines from points */
		p = points[i]
		q = points[(i+1)%points.length]
		r = points[(i+2)%points.length]
		
		if(!(p && q && r))
		    continue

        line(p[0], p[1], q[0], q[1])

		if(p[1] == q[1]) continue               /* no horizontals */

		m = null                                /* slope */
		if(p[0] != q[0])
		    m = (1.0*q[1]-p[1])/(q[0]-p[0])
		
		eflag = false                           /* endpoint flag */
		if((q[1]-p[1] > 0) != (q[1]-r[1] >= 0))
			eflag = true
		
		var [ylo, yhi] = [p[1], q[1]]           /* y's span */
		if(ylo > yhi)
			[ylo,yhi]=[yhi,ylo]

		scan_start = Math.min(scan_start, ylo)
		scan_end = Math.max(scan_end, yhi)
		lines.push({'ylo':ylo,'yhi':yhi,'p':p,'q':q,'m':m,'eflag':eflag})
	}

    /* round to magic boundary */
    tmp = scan_start
    scan_start = Math.floor((scan_start * 1000000)/390625) * 0.390625
	for(y=scan_start; y<=scan_end; y+=.1953125) {    /* scan */
		intersects = []                         /* collect intersections */
		for(l of lines) {
			if(y<l['ylo'] || y>l['yhi'])
				continue

			x = null
			if(l['m']==null)
				x = l['p'][0]
			else
				x = (y-l['p'][1])/l['m'] + l['p'][0]

			if(! (y==l['q'][1] && l['eflag']) )
				intersects.push(x)
		}
		
        intersects.sort()                       /* draw intersections */
		for(i=0; i<intersects.length; i+=2) {
		    x0 = intersects[i]
		    x1 = intersects[i+1]
		    
		    for(j=0; j<lrepeat; ++j)
	            line(x0,y,x1,y)
		}
	}
}
