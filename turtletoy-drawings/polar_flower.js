// created by Andrew Lamoureux (andrewl) - 2019
// License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

Canvas.setpenopacity(1);
const turtle = new Turtle();
const zoom = 16

function line(x1,y1,x2,y2)
{
    turtle.penup();
    turtle.goto(x1,y1);
    turtle.pendown();
    turtle.goto(x2,y2);
}

function map(x,y)
{
    // cartesian -> polar
    r = Math.sqrt(x*x + y*y)
    a = Math.atan2(y,x)
        
    var u=0, v=0;
    if(r != 0) {
        // polar -> cartesian but with r=(1/r)
        u = (1/r) * Math.cos(a)
        v = (1/r) * Math.sin(a)
    }
    
    return [u, v]
}

function walk(i)
{
    previous = undefined
    
    for(var y=-100; y<100; y=y+1) {
        for(var x=-100; x<100; x=x+1) {
            var [u,v] = map(x,y)
            u *= zoom
            v *= zoom
            
            // cartesian -> screen
            i_ = -100 + (u+1)/2.0 * 200
            j_ = -100 + (1-v)/2.0 * 200
            
            // draw lines
            if(previous != undefined) {
                line(i_,j_,previous[0], previous[1])
                line(j_,i_,previous[1], previous[0])
            }
            previous = [i_,j_]
        }
    }
    
    return false;
}

