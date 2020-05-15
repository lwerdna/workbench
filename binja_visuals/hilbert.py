#!/usr/bin/env python

# draw binary (as decomposed with Binary Ninja) and outline functions in white
#
# $ ./thisfile.py /path/to/mybinary.exe
#
# then check /tmp/tmp.png

import os
import sys
import math

import binaryninja
from binaryninja.binaryview import BinaryViewType

from PIL import Image, ImageDraw
from sfcurves.hilbert import forward, reverse, outline, generator

from intervaltree import IntervalTree, Interval

# globals
n = None
draw = None

def draw_region(start, stop, color1='#00ff00', color2=None):
	global n, draw
	trace = wall_follower(n, start, stop, forward, reverse)
	draw.polygon(trace, outline=color1, fill=color2)

#------------------------------------------------------------------------------
# main()
#------------------------------------------------------------------------------

if __name__ == '__main__':
	bv = BinaryViewType.get_view_of_file(sys.argv[1])
	bv.update_analysis_and_wait()

	assert bv.start == bv.segments[0].start
	assert bv.end == bv.segments[-1].end
	assert len(bv) == bv.end - bv.start # note! this includes gaps between segments!

	# collect segments
	it_segments = IntervalTree()
	for segment in bv.segments:
		it_segments.add(Interval(segment.start, segment.end, segment))
	# collect sections
	it_sections = IntervalTree()
	for section in bv.sections.values():
		it_sections.add(Interval(section.start, section.end, section))
	# decorate each function with an IntervalTree of its spanned bytes
	for function in bv.functions:
		itree = IntervalTree()
		for bblock in function:
			itree.add(Interval(bblock.start, bblock.end))
		function.itree = itree

	# check that sections are in one segment
	for section in bv.sections.values():
		intervals = it_segments.overlap(section.start, section.end)
		assert len(intervals) == 1
		segment = intervals.pop().data
		print('section %s is in segment %s' % (section, segment))
	# check functions are in one section
	for function in bv.functions:
		intervals = it_sections.overlap(function.basic_blocks[0].start, function.basic_blocks[0].end)
		assert len(intervals) == 1
		section = intervals.pop().data
		print('function %s is in section %s' % (function, section))

	n_backed_bytes = sum([interval.length() for interval in it_segments])
	width = 2
	length = 4
	while length < n_backed_bytes:
		width *= 2
		length *= 4

	from palettes import viridis as palette
	img = Image.new('RGB', (width,width))
	draw = ImageDraw.Draw(img)

	gen = generator(length)
	for segment in bv.segments:
		for addr in range(segment.start, segment.end):
			byte = bv.read(addr, 1)
			color = palette[byte[0]] if byte else '#000000'
			(x,y) = next(gen)
			draw.point((x,y), fill=color)
	del draw

	fpath = '/tmp/tmp.png'
	print('saving %s' % fpath)
	img.save(fpath)
