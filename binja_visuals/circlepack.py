#!/usr/bin/env python
# Draw a binary as a circle-packed diagram.
#
# Usage:
# $ ./thisfile.py /path/to/binary.bndb
# writes /tmp/tmp.png

import os, sys

import binaryninja
from binaryninja.binaryview import BinaryViewType

from PIL import Image, ImageDraw, ImageFont
import circlify
from circlify import Circle

# globals
(width, height) = (1024, 1024)
font = ImageFont.truetype('Andale Mono', 12)
(tw8,th8) = font.getsize('12345678')

def rectangle(draw, x, y, bgcolor):
	global font
	(w,h) = (x1-x0, y1-y0)

	label = settings['label']

	for font_size in range(12,1,-1):
		font = ImageFont.truetype('Andale Mono', font_size)
		(tw,th) = font.getsize(label)
		if tw<w and th<h: break
	
	draw.rectangle((x0, y0, x1-1, y1-1), outline=settings['outline'], fill=settings['fill'])

	(x,y) = (x0+w//2 - tw//2, y0+h//2-th//2)
	draw.text((x,y), label, font=font, fill=settings['text_color'])

if __name__ == '__main__':
	bv = BinaryViewType.get_view_of_file(sys.argv[1])
	bv.update_analysis_and_wait()

	img = Image.new('RGB', (width,width))
	draw = ImageDraw.Draw(img)

	seg2data = {}
	for seg in bv.segments:
		seg2data[seg] = {'id':str(seg), 'datum':len(seg), 'children':[]}

	scn2data = {}
	for scn in bv.sections.values():
		data = {'id':scn.name, 'datum':len(scn), 'children':[]}
		containing_segment = bv.get_segment_at(scn.start)
		seg2data[containing_segment]['children'].append(data)
		scn2data[scn] = data

	for func in bv.functions:
		length = sum([len(x) for x in func.basic_blocks])
		data = {'id':func.name, 'datum':length}
		containing_section = bv.get_sections_at(func.start)[0]
		scn2data[containing_section]['children'].append(data)

	data = list(seg2data.values())
	print('input data:')
	import pprint
	pprint.pprint(data, width=1)
	print('circle packing...')
	circles = circlify.circlify(data, show_enclosure=True)
	print(circles)

	#
	# draw it
	#
	print('drawing...')
	img = Image.new('RGB', (width,width))
	draw = ImageDraw.Draw(img)

	for circle in circles:
		# PIL is (0,0) at upper left
		# circlify is Cartesian with 0,0 at center and [-1,1] span of x,y

		x = (circle.x + 1)/2 * width
		y = (circle.y + 1)/2 * height
		r = circle.r/2 * width

		color_fill = 'red'
		color_outline = 'white'
		extra = circle.ex
		if extra:
			name = extra['id']
			if name.startswith('<segment'):
				color_fill = '#440154'
			if name.startswith('.'):
				color_fill = '#3B518A'

		if circle.level == 0: continue
		if circle.level == 1:
			r += 8
			color_outline = color_fill

		# ellipse() is given top-left and bottom-right of corners
		draw.ellipse((x-r, y-r, x+r, y+r), fill=color_fill, outline=color_outline)

		label = extra['id']
		font = ImageFont.truetype('Andale Mono', 12)
		(tw,th) = font.getsize(label)
		if circle.level == 1:
			draw.rectangle((x-tw//2, y-r-th//2, x+tw//2, y-r+th//2), outline=color_fill, fill=color_fill)
			draw.text((x-tw//2, y-r-th//2), label, font=font, fill='white')
		elif circle.level == 2:
			draw.text((x-tw//2, y-r), label, font=font, fill='white', outline='white')
		else:
			for font_size in range(12,1,-1):
				font = ImageFont.truetype('Andale Mono', font_size)
				(tw,th) = font.getsize(label)
				if tw<2*r and th<2*r: break
			draw.text((x-tw//2, y-th//2), label, font=font, fill='white', outline='white')

	img.save('/tmp/tmp.png')
