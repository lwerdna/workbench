#!/usr/bin/env python

import sys
import random

from PIL import Image, ImageDraw
from sfcurves import hilbert_d2xy_wikipedia as d2xy, hilbert_xy2d_wikipedia as xy2d, wall_follower

n = 64

for d in range(4000):
	(x,y) = d2xy(64**2, d)
	d_ = xy2d(64**2, x, y)

	if d != d_:
		print('%d,%d mapped to d=%d but got unmapped to %d' % (x,y,d,d_))
		assert(False)


# [start, stop)
def draw_hilbert(start, stop, color='#ffffff'):
	global n

	# in hilbert space we'll have a 64x64 image, but in png space we'll
	# make it 64x64 and scale by 4
	pts = [d2xy(n, x) for x in range(start, stop)]
	lines = zip(pts[:-1], pts[1:])
	for line in lines:
		((x1,y1),(x2,y2)) = line
		(x1,y1,x2,y2) = map(lambda x: x*4+1, (x1,y1,x2,y2))
		#print('drawing line (%d,%d) -> (%d,%d)' % (x1,y1,x2,y2))
		draw.line((x1,y1,x2,y2), width=1, fill=color)

def draw_region(start, stop, color='#00ff00'):
	trace = wall_follower(n, start, stop, d2xy, xy2d)
	trace = [(4*p[0]+1, 4*p[1]+1) for p in trace]
	draw.polygon(trace, outline=color)

if __name__ == '__main__':
	img = Image.new('RGB', (4*n,4*n))
	draw = ImageDraw.Draw(img)

	# background
	draw_hilbert(0, n**2, '#ff0000')

	marks = [0] + [random.randint(0,n**2-1) for x in range(10)] + [n**2]
	marks = sorted(marks)
	for (start,stop) in zip(marks[:-1], marks[1:]):
		draw_region(start, stop)

	del draw
	fpath = '/tmp/tmp.png'
	print('saving %s' % fpath)
	img.save(fpath)

