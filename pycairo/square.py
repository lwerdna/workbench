#!/usr/bin/env python

import math
import cairo
from PIL import Image

# square "radius"
square_r = 64

# INPUT:
#       cr: cairo context
#      pos: 2-tuple of position, center
#   stroke: 3-tuple of outline color
#     fill: 3-tuple of fill color
def drawSquare(cr, pos, stroke, fill):
	(x,y) = pos

	cr.set_source_rgb(*stroke)
	cr.set_line_width(4)

	cr.rectangle(x, y, square_r*2, square_r*2)
	cr.stroke_preserve()

	cr.set_source_rgb(*fill)
	cr.fill()

if __name__ == '__main__':
	surface = cairo.ImageSurface(cairo.FORMAT_RGB24, 640, 480)
	cr = cairo.Context(surface)

	drawSquare(cr, (128,128), (1,1,1), (1,0,0))	

	surface.write_to_png("/tmp/quick.png")
