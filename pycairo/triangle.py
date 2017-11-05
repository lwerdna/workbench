#!/usr/bin/env python

import math
import cairo
from PIL import Image

# triangle "radius"
triangle_r = 64

# INPUT:
#       cr: cairo context
#      pos: 2-tuple of position, center
#   stroke: 3-tuple of outline color
#     fill: 3-tuple of fill color
def drawTriangle(cr, pos, stroke, fill):
	(x,y) = pos

	cr.set_source_rgb(*stroke)
	cr.set_line_width(4)

	ratio = math.sqrt(3)/2.0
	p1 = (x, y-triangle_r)
	p2 = (x - ratio*triangle_r, y + triangle_r*(1/3.0))
	p3 = (x + ratio*triangle_r, y + triangle_r*(1/3.0))

	cr.move_to(*p1)
	cr.line_to(*p2)
	cr.line_to(*p3)
	cr.line_to(*p1)
	cr.line_to(*p2)
	cr.stroke_preserve()

	cr.set_source_rgb(*fill)
	cr.fill()

if __name__ == '__main__':
	surface = cairo.ImageSurface(cairo.FORMAT_RGB24, 640, 480)
	cr = cairo.Context(surface)

	drawTriangle(cr, (128,128), (1,1,1), (1,0,0))	

	surface.write_to_png("/tmp/quick.png")
