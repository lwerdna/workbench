#!/usr/bin/env python

import math
import cairo
from PIL import Image

def write(message, color, x, y, opts):

	cr.select_font_face(opts['font'])
	cr.set_font_size(opts['size'])

	(x_bear, y_bear, width, height, x_advance, y_advance) = cr.text_extents(message)

	pos_x = x - width/2
	pos_y = y + height/2

	if opts['rotate']:
		cr.save()
		radians = opts['rotate'] * math.pi / 180
		cr.translate(x, y)
		cr.rotate(radians)
		cr.translate(-x, -y) 

	if opts['backdrop']:
		cr.set_source_rgb(*opts['backdrop'])
		cr.rectangle(pos_x-4, pos_y-height-4, width+8, height+8)
		cr.fill()

	cr.set_source_rgb(*color)
	cr.move_to(pos_x, pos_y)
	cr.show_text(message)

	if opts['rotate']:
		cr.restore()

if __name__ == '__main__':
	surface = cairo.ImageSurface(cairo.FORMAT_RGB24, 640, 480)
	cr = cairo.Context(surface)

	writeOpts = { 'font':'Georgia', 'size':15, 'backdrop':(1,0,0), 'rotate':-45 }
	write('Hello, world!', (0,1,0), 128, 128, writeOpts)

	surface.write_to_png("/tmp/quick.png")
