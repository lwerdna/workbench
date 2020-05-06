#!/usr/bin/env python

# draw functions (identified with Binary Ninja) as Hilbert curve regions
# usage:
# ./bin2hilbert.py /path/to/mybinary.exe
#
# then check /tmp/tmp.png

import os
import sys
import math

import binaryninja
from binaryninja.binaryview import BinaryViewType

from PIL import Image, ImageDraw
from sfcurves import hilbert_d2xy_wikipedia as d2xy, hilbert_xy2d_wikipedia as xy2d, wall_follower

# globals
n = None
draw = None

# [start, stop)
def draw_hilbert(start, stop, color='#ffffff'):
	global n, draw

	pts = [d2xy(n, x) for x in range(start, stop)]
	lines = zip(pts[:-1], pts[1:])
	for line in lines:
		((x1,y1),(x2,y2)) = line
		#print('drawing line (%d,%d) -> (%d,%d)' % (x1,y1,x2,y2))
		draw.line((x1,y1,x2,y2), width=1, fill=color)

def draw_region(start, stop, color1='#00ff00', color2=None):
	global n, draw
	trace = wall_follower(n, start, stop, d2xy, xy2d)
	draw.polygon(trace, outline=color1, fill=color2)

#------------------------------------------------------------------------------
# main()
#------------------------------------------------------------------------------

if __name__ == '__main__':
	fpath = sys.argv[1]

	addr2name = {}
	addr2end = {}
	fpath_funcs = '/tmp/' + os.path.basename(fpath) + '_functions.txt'
	print('searching for cached functions in %s' % fpath_funcs)
	if os.path.exists(fpath_funcs):
		print('found!')
		with open(fpath_funcs) as fp:
			for line in fp.readlines():
				(start, end, name) = line.split()
				addr2name[int(start,16)] = name
				addr2end[int(start,16)] = int(end,16)
	else:
		print('not found! binja time!')
		print('get_view_of_file()')
		bv = BinaryViewType.get_view_of_file(fpath)
		print('update_analysis_and_wait()')
		bv.update_analysis_and_wait()
		print('done!')
		for f in bv.functions:
			addr2name[f.start] = f.symbol.full_name
			addr2end[f.start] = f.start + f.total_bytes

		print('writing %s' % fpath_funcs)
		with open(fpath_funcs, 'w') as fp:
			for a in addr2name:
				fp.write('%X %X %s\n' % (a, addr2end[a], addr2name[a]))

	print('loaded %d functions' % len(addr2name))
	lowest = min(addr2name)
	highest = max(addr2end.values())
	print('lowest address: 0x%04X' % lowest)
	print('highest address: 0x%04X' % highest)

	pixels = 1
	while pixels < (highest-lowest):
		pixels *= 4
	n = int(math.sqrt(pixels))
	print('n:', n)

	img = Image.new('RGB', (n,n))
	draw = ImageDraw.Draw(img)

	# background
	#draw_hilbert(0, n**2, '#ff0000')

	# palette is "tab20" from matplotlib
	palette_i = 0
	palette = [
		'#1F77B4', '#AEC7E8', '#FF7F0E', '#FFBB78', '#2CA02C', '#98DF8A', '#D62728', '#FF9896',
		'#9467BD', '#C5B0D5', '#8C564B', '#C49C94', '#E377C2', '#F7B6D2', '#7F7F7F', '#C7C7C7',
		'#BCBD22', '#DBDB8D', '#17BECF', '#9EDAE5'
	]

	for a in addr2name:
		addr_start = a
		addr_end = addr2end[a]

		if addr_end - addr_start < 4:
			continue

		print('drawing %s [0x%04X, 0x%04X)' % (addr2name[a], addr_start, addr_end))
		draw_region(addr_start - lowest, addr_end - lowest, None, palette[palette_i])
		palette_i = (palette_i+1) % len(palette)

	del draw
	fpath = '/tmp/tmp.png'
	print('saving %s' % fpath)
	img.save(fpath)
