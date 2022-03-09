// created by Andrew Lamoureux (andrewl) - 2018
// License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

// You can find the Turtle API reference here: https://turtletoy.net/syntax
Canvas.setpenopacity(.25);

// Global code will be evaluated once.
const turtle = new Turtle();
turtle.pendown()

const screen_width = 200
const screen_height = 200

var xrot = Math.PI/3.7 /* in radians */

const scale = 19
const shifty = -19
const shiftx = 4
const ticks_toroid = 100
const ticks_cross_section = 50
const npoints = ticks_toroid * ticks_cross_section

function get_knot_point(i) {
    // point index -> (t, u)
    ti = Math.floor(i/ticks_cross_section)
    ui = i % ticks_cross_section
    
    t = ti/ticks_toroid * 2*Math.PI
    u = ui/ticks_cross_section * 2*Math.PI
            
    // eval parametric equations -> polar coords
    r0 = scale*(3 + msin(t) + mcos(u))
    theta = 2*t
    z = scale*(msin(u) + 2*mcos(t))
            
    // polar -> cartesian
    x = r0*mcos(theta) + shiftx
    y = r0*msin(theta) + shifty
    
    return [x,y,z]
}

// The walk function will be called until it returns false.
function walk(i) {
    // this point
    pi = get_knot_point(i)
    // next point in this cross section
    if((i+1) % ticks_cross_section == 0)
        pj = get_knot_point(i-ticks_cross_section+1)
    else
        pj = get_knot_point(i+1)
    // point in next cross section
    p3 = get_knot_point(i+ticks_cross_section)
    
    pi = rotX(xrot,pi)
    pj = rotX(xrot,pj)
    p3 = rotX(xrot,p3)
    
    pi = project(pi)
    pj = project(pj)
    p3 = project(p3)
    
    turtle.penup()
    turtle.goto(p3[0], p3[1])
    turtle.pendown()
    turtle.goto(pi[0], pi[1])
    turtle.goto(pj[0], pj[1])
    turtle.goto(p3[0], p3[1])
    
    //  compute vector perpendicular to their plane and test if z coord is positive (facing us)
    //  or negative (facing away)
    if(vec3_cross(vec3_sub(pj,pi), vec3_sub(p3,pi) )[2] > 0.0)
    {
        for(k in [1,2,3]) {
            turtle.penup()
            turtle.goto(p3[0], p3[1])
            turtle.pendown()
            turtle.goto(pi[0], pi[1])
            turtle.goto(pj[0], pj[1])
            turtle.goto(p3[0], p3[1])
        }
    }
    
    return i<npoints
}

function project(p)
{
    x = p[0]
    y = p[1]
    z = p[2]
    z = z + 180
    return [ (x/z)*screen_width, (y/z)*screen_height ];
}

function mcos(x) {
    return Math.cos(x);
}

function msin(x) {
    return Math.sin(x);
}

function vec3_add(a,b) {
    return [a[0]+b[0],a[1]+b[1],a[2]+b[2]];
}

function vec3_sub(a,b) {
    return [a[0]-b[0],a[1]-b[1],a[2]-b[2]];
}

function vec3_cross(a,b) {
    return [
        a[1]*b[2]-b[1]*a[2],
        a[2]*b[0]-b[2]*a[0],
        a[0]*b[1]-b[0]*a[1]
    ];
}

function rotX(ph,v) {
    return [ v[0],v[1]*mcos(ph)+v[2]*msin(ph), v[2]*mcos(ph)-v[1]*msin(ph) ];
}


