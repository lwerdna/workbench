#!/usr/bin/env python

import math
import cairo
from PIL import Image

# hex "radius"
hex_r = 64

# INPUT:
#       cr: cairo context
#      pos: 2-tuple of position, center
#   stroke: 3-tuple of outline color
#     fill: 3-tuple of fill color
def drawHex(cr, pos, stroke, fill):
	(x,y) = pos

	cr.set_source_rgb(*stroke)
	cr.set_line_width(1)

	ratio = math.sqrt(3)/2.0
	cr.move_to(x + hex_r, y)
	cr.line_to(x + hex_r/2.0, y - ratio*hex_r)
	cr.line_to(x - hex_r/2.0, y - ratio*hex_r)
	cr.line_to(x - hex_r, y)
	cr.line_to(x - hex_r/2.0, y + ratio*hex_r)
	cr.line_to(x + hex_r/2.0, y + ratio*hex_r)
	cr.line_to(x + hex_r, y)
	cr.stroke_preserve()

	cr.set_source_rgb(*fill)
	cr.fill()

if __name__ == '__main__':
	surface = cairo.ImageSurface(cairo.FORMAT_RGB24, 640, 480)
	cr = cairo.Context(surface)

	drawHex(cr, (128,128), (0,0,0), (1,0,0))	

	surface.write_to_png("/tmp/quick.png")
