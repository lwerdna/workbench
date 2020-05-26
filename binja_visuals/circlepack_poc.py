#!/usr/bin/env python

import os
import sys
import math

import binaryninja
from binaryninja.binaryview import BinaryViewType

from PIL import Image, ImageDraw, ImageFont
import circlify as circ

# globals
(width, height) = (1024, 1024)
font = ImageFont.truetype('Andale Mono', 12)
(tw8,th8) = font.getsize('12345678')

def rectangle(draw, x0, y0, x1, y1, settings):
	global font
	(w,h) = (x1-x0, y1-y0)
	draw.rectangle((x0, y0, x1-1, y1-1), outline=settings['outline'], fill=settings['fill'])

	label = settings['label']

	for font_size in range(12,1,-1):
		font = ImageFont.truetype('Andale Mono', font_size)
		(tw,th) = font.getsize(label)
		if tw<w and th<h: break
	(tw,th) = font.getsize(label)

	if settings.get('center_text', False):
		(x,y) = (x0+w//2 - tw//2, y0+h//2-th//2)
	else:
		(x,y) = (x0+w//2 - tw//2, y0)
	draw.text((x,y), label, font=font, fill=settings['text_color'])

if __name__ == '__main__':


	data = [0.05, {'id': 'a2', 'datum': 0.05},
		{'id':'a0','datum':0.8,'children':[0.3,0.2,0.2,0.1],},
		{'id':'a1','datum':0.1,'children':
		[{'id':'a1_1','datum':0.05},{'datum':0.04},0.01],},
	]
	circles = circ.circlify(data, show_enclosure=True)

	img = Image.new('RGB', (width,width))
	draw = ImageDraw.Draw(img)

	for circle in circles:
		# PIL is (0,0) at upper left
		# circlify is Cartesian with 0,0 at center and [-1,1] span of x,y
		
		x = (circle.x + 1)/2 * width
		y = (circle.y + 1)/2 * height
		r = circle.r/2 * width

		# ellipse() is given top-left and bottom-right of corners
		draw.ellipse((x-r, y-r, x+r, y+r), fill='red', outline='white')
	img.save('/tmp/tmp.png')

	print(circles)
	sys.exit(-1)

	bv = BinaryViewType.get_view_of_file(sys.argv[1])
	bv.update_analysis_and_wait()

	img = Image.new('RGB', (width,width))
	draw = ImageDraw.Draw(img)

	img.save('/tmp/tmp.png')

	# calculate segments
	seg2rect = {}
	sizes = [len(s) for s in bv.segments]
	labels = list(map(str, range(len(bv.segments))))
	tm = treemap.squarify(sizes=sizes, x=0, y=0, dx=width, dy=height, labels=labels)
	for entry in tm:
		rcoords = (entry['x'], entry['y'], entry['x']+entry['dx'], entry['y']+entry['dy'])
		segment_index = int(entry['label'])
		seg2rect[bv.segments[segment_index]] = rcoords

	# draw segments
	for (seg, rect) in seg2rect.items():
		settings = {'outline':(0,0,0), 'fill':(0xbe,0xae,0xd4), 'text_color':(0,0,0), 'label':str(seg)}
		rectangle(draw, *rect, settings)

	# calculate sections
	sec2rect = {}
	#for i in range(0):
	margin = th8+4
	for (seg, rect) in seg2rect.items():
		sections = [s for s in bv.sections.values() if s.start >= seg.start and s.end <= seg.end]
		print('in segment %s we have sections:' % str(seg))
		print('\n'.join(map(str,sections)))

		sizes = [len(s) for s in sections]
		labels = list(map(str, range(len(sections))))
		tm = treemap.squarify(sizes=sizes, x=rect[0]+margin, y=rect[1]+margin, dx=rect[2]-rect[0]-2*margin, dy=rect[3]-rect[1]-2*margin, labels=labels)
		#print(tm)
		for entry in tm:
			rcoords = (entry['x'], entry['y'], entry['x']+entry['dx'], entry['y']+entry['dy'])
			section_index = int(entry['label'])
			sec2rect[sections[section_index]] = rcoords

	# draw sections
	print(sec2rect)
	for (sec, rect) in sec2rect.items():
		settings = {'outline':(0,0,0), 'fill':(0x7F,0xC9,0x7F), 'text_color':(0,0,0), 'label':sec.name}
		rectangle(draw, *rect, settings)

	# calculate/draw functions
	for (sec, rect) in sec2rect.items():
		funcs = []
		lengths = []

		for f in bv.functions:
			length = sum([len(z) for z in [bb for bb in f.basic_blocks if bb.start >= sec.start and bb.end <= sec.end]])
			if length:
				print('adding function ', f.name)
				funcs.append(f)
				lengths.append(length)

		if not lengths:
			continue

		labels = list(map(str, range(len(funcs))))
		print('sizes: ', lengths)
		print('labels: ', labels)
		tm = treemap.squarify(sizes=lengths, x=rect[0]+margin, y=rect[1]+margin, dx=rect[2]-rect[0]-2*margin, dy=rect[3]-rect[1]-2*margin, labels=labels)
		print(tm)
		for entry in tm:
			rcoords = (entry['x'], entry['y'], entry['x']+entry['dx'], entry['y']+entry['dy'])
			func = funcs[int(entry['label'])]
			settings = {'outline':(0,0,0), 'fill':(0xFD,0xC0,0x86), 'text_color':(0,0,0), 'label':func.name+'()', 'center_text':True}
			print('drawing function %s' % func.name)
			rectangle(draw, *rcoords, settings)

	img.save('/tmp/tmp.png')
