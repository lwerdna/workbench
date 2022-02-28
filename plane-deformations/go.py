#!/usr/bin/env python

import os, sys
from math import *

from PIL import Image

width = 256

# given a cartesian (x, y), return a texture coordinate (u, v)
# "at destination coordinate (x, y), where in the texture should I reach for a color?"
# all x, y, u, v in [0, 1]
def mapping_cartesian(x, y, technique):
    # cartesian -> polar
    r = sqrt(x*x + y*y);
    a = atan2(y, x)
    #print 'cartesian (%f,%f) -> polar(r=%f, angle=%f)' % (x,y,r,a)
        
    (u,v) = (0,0)

    # lense
    if technique == 0:
        if r>=0 and r<=1:
            dome_a = asin(r)
            dome_r = tan(dome_a)
            u = dome_r * cos(a)
            v = dome_r * sin(a)

    # inverse polar
    elif technique == 1:
        if r != 0:
            u = (1/r)*cos(a)
            v = (1/r)*sin(a)

    # circular wavy
    elif technique == 2:
        u = x*cos(2*r) - y*sin(2*r)
        v = y*cos(2*r) + x*sin(2*r)
   
    # tunnel
    elif technique == 3:
        denom = r + .5*x
        if denom != 0:
            u = .3 / denom
            v = 3 * a/pi

    # circular wavy #2
    elif technique == 4:
        u = r * cos(a + r)
        v = r * sin(a + r)

    # pentalobe
    elif technique == 5:
        denom = 1/(r+.5+.5*sin(5*a))
        if denom != 0:
            u = 1/denom
            v = a*3/pi

    # cave crawl
    elif technique == 6: # cave crawl
        if y != 0:
            u = x/abs(y)
            v = 1/abs(y)

    # ----

    elif technique == 7: # tunnel
        denom = r
        if denom != 0:
            u = 1/denom
            v = a

    elif technique == 8: # don't work
        if r!=0:
            u = .02*y + .03*cos(a*3)/r
            v = .02*x + .03*sin(a*3)/r

    elif technique == 9: # don't work
        denom = .11+r*.5
        if denom != 0:
            u = .1*x/denom
            v = .1*y/denom

    elif technique == 10: # don't work
        u = .5*a/pi
        v = sin(7*r)

    elif technique == 11: # circular wavy #2
        u = r*cos(a+r)
        v = r*sin(a+r)

    elif technique == 12: # lens cylinder
        i_ = (u+1)/2.0 * width
        j_ = (1-v)/2.0 * width

    return (u,v)

def mapping_screen(i, j, technique):
    # screen -> cartesian [-1,1]
    x = -1 + 2*(1.0*i/width)
    y = 1 - 2*(1.0*j/width)
    #print 'screen (%d,%d) -> cartesian (%f,%f)' % (i,j,x,y)

    (u, v) = mapping_cartesian(x, y, technique)

    # u,v -> screen
    i_ = (u+1)/2.0 * width
    j_ = (1-v)/2.0 * width
    #print '(i_,j_) = (%d,%d)' % (i_,j_)

    return (int(i_) % width, int(j_) % width)

def do_technique(technique, fpath, x_bias=0, y_bias=0):
    img = Image.new('RGB', (width, width))

    for x in range(width):
        for y in range(width):
            coords_source = mapping_screen(x, y, technique)

            if x_bias or y_bias:
                coords_source = ((coords_source[0] + x_bias) % width, (coords_source[1] + y_bias) % width)

            pixel = texture.getpixel(coords_source)
            img.putpixel((x, y), pixel)

    print('writing %s' % fpath)
    img.save(fpath)

if __name__ == '__main__':
    texture = Image.open('chess_%d.png' % width).convert('RGB')

    if sys.argv[1:] and sys.argv[1] == 'animate':
        # generate an animated inverse polar

        for frame in range(32):
            do_technique(1, '/tmp/frame_%04d.png' % frame, frame, frame)

        os.system('convert -delay 2 /tmp/frame_*.png -loop 0 /tmp/tmp.gif')

    else:
        for technique in range(7):
            do_technique(technique, '/tmp/tmp%d.png' % technique)

