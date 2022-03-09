// created by Andrew Lamoureux (andrewl) - 2019
// License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

Canvas.setpenopacity(1);
const turtle = new Turtle();
const spokes = 11
const anglestep = 2*Math.PI/spokes

function line(a,b) { turtle.penup(); turtle.goto(a[0],a[1]); turtle.pendown(); turtle.goto(b[0],b[1]); }
function rot(p, a) { return [p[0]*mcos(a)-p[1]*msin(a), p[1]*mcos(a)+p[0]*msin(a)] }
function mcos(a) { return Math.cos(a) }
function msin(a) { return Math.sin(a) }
function gen(r, a) {
    points = [[.6,0],[1, .9],[1.5, .25],[1.25, 0],[1.5, -.25],[1, -.9]]
    points = points.map(p => [p[0]*r/3, p[1]*r/3]) // scale
    points = points.map(p => rot(p, a)) // rotate
    var [dx,dy] = rot([r,0], a)
    points = points.map(p => [p[0]+dx, p[1]+dy]) // shift
    return points
}

r = .5
rg = 1.26
function walk(ring) {
    for(var spoke=0; spoke<spokes; spoke++) {
        var a = spoke*anglestep + (ring%2)*anglestep/2
        var [p1,p2,p3,p4,p5,p6] = gen(r, a)
        line(p1,p2); line(p2,p3); line(p3,p4); line(p4,p5); line(p5,p6); line(p6,p1)
        if(ring>2) {
            line(p1,gen((1/rg)*(1/rg)*r, a)[3])
            line(p2,gen((1/rg)*r, a+anglestep/2)[4])
            line(p6,gen((1/rg)*r, a-anglestep/2)[2])
        }
    }
    
    r = rg*r
    return ring < 30;
}
