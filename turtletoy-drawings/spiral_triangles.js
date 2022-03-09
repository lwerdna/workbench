// created by Andrew Lamoureux (andrewl) - 2019
// License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

Canvas.setpenopacity(1);
const turtle = new Turtle();

function walk(i)
{
    nspokes = 22
    ndots = 41
    spacing = 5
    spin_speed = 1.6
    tri_rot = .78
    ysizer = 7
    
    fbradius = 150
    
    for(spoke=0; spoke<nspokes; ++spoke) {
        angle = (spoke/nspokes)*2*Math.PI

        for(ri=3; ri<ndots; ++ri) {
            r = ri * (fbradius/ndots)
            
            /* increase angle as r increases
                (spiral effect) */
            angle_ = angle + spin_speed*r/fbradius*Math.PI

            var [x,y] = [r*Math.cos(angle_), r*Math.sin(angle_)]
            
            trisize = 1 + (r/150)*5 + ysizer*((y+100)/200)**2
            triangle(x, y, trisize, tri_rot*angle)
        }
    }

    triangle(0, 0, 10, 0)

    return false;
}
/* scan-line polygon fill
    WARNNG: basic implementation, no optimizations here */
function polyfill(points)
{
	lines = []
    scan_start = 100
    scan_end = -100

	for(i=0; i<points.length; i++) {            /* collect lines from points */
		p = points[i]
		q = points[(i+1)%points.length]
		r = points[(i+2)%points.length]

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

	for(y=scan_start; y<=scan_end; y+=.15) {    /* scan */
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
	        line(x0,y,x1,y)
		}
	}
}

function rotate(p, angle)
{
	[x,y] = [p[0], p[1]]
	//console.log('rotate('+x+','+y+')')
	return [x*Math.cos(angle) - y*Math.sin(angle),
	        y*Math.cos(angle) + x*Math.sin(angle)]
}

function shift(point, x, y)
{
	return [point[0]+x, point[1]+y]
}

function line(x0,y0,x1,y1)
{
    //console.log('line('+x0+','+y0+','+x1+','+y1+')')
    turtle.penup()
    turtle.goto(x0,y0)
    turtle.pendown()
    turtle.goto(x1,y1)
}

function triangle(x, y, side, angle)
{
    //console.log('triangle('+x+','+y+')')
    dx = side/2.0
    dya = side * (1/Math.sqrt(3))
    dyb = side * (1/(2*Math.sqrt(3)))
    
    var p0 = [0, -dya]
    var p1 = [side/2.0, dyb]
    var p2 = [-side/2.0, dyb]

    var [p0,p1,p2] = [rotate(p0,angle), rotate(p1,angle), rotate(p2,angle)]
    var [p0,p1,p2] = [shift(p0,x,y), shift(p1,x,y), shift(p2,x,y)]
    polyfill([p0,p1,p2])
}

