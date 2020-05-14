#!/usr/bin/env python

# display functions identified with BinaryNinja in a PySimpleGui interface

import io
import os
import sys
import math
import base64

import binaryninja
from binaryninja.binaryview import BinaryViewType

from PIL import Image, ImageDraw
from sfcurves import hilbert_d2xy_wikipedia as d2xy, hilbert_xy2d_wikipedia as xy2d, wall_follower

import PySimpleGUI as sg

# globals
n = None
draw = None
width = None
height = None

# [start, stop)
def draw_hilbert(start, stop, color='#ffffff'):
	global n, draw

	pts = [d2xy(n, x) for x in range(start, stop)]
	lines = zip(pts[:-1], pts[1:])
	for line in lines:
		((x1,y1),(x2,y2)) = line
		#print('drawing line (%d,%d) -> (%d,%d)' % (x1,y1,x2,y2))
		draw.line((x1,y1,x2,y2), width=1, fill=color)

def draw_region(start, stop, color1=None, color2=None):
	global n, draw
	trace = wall_follower(n, start, stop, d2xy, xy2d)
	trace = list(map(lambda p: (4*p[0]+1, height - (4*p[1]+1)), trace))
	draw.polygon(trace, outline=color1, fill=color2)

def img_to_b64gif(img):
	# PIL -> gif -> string
	gif = None
	with io.BytesIO() as output:
		img.save(output, format="GIF")
		gif = output.getvalue()

	# gif string -> base64
	return base64.b64encode(gif)

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
	width = n*4
	height = n*4

	# generate background PIL image
	img_background = Image.new('RGB', (width, height))
	draw = ImageDraw.Draw(img_background)
	for a in addr2name:
		addr_start = a
		addr_end = addr2end[a]
		if addr_end - addr_start < 4:
			continue
		print('drawing %s [0x%04X, 0x%04X)' % (addr2name[a], addr_start, addr_end))
		draw_region(addr_start - lowest, addr_end - lowest, '#FFFFFF')
	del draw

	# start
	graph = sg.Graph((width,height), (0,0), (width-1, height-1), key='_GRAPH_', pad=(0,0), enable_events=True)
	gui_rows = [
				[graph],
				[sg.Text('function:'), sg.InputText('dummy', do_not_clear=True, key='_FUNCTION_')],
				[sg.Text('start:'), sg.InputText('00000000', do_not_clear=True, key='_START_')],
				[sg.Text('end:'), sg.InputText('DEADBEEF', do_not_clear=True, key='_END_')],
				[sg.Quit()]
			]

	window = sg.Window('Hilbert Curve Region', auto_size_text=True).Layout(gui_rows)

	initial_loop = True
	while (True):
		# This is the code that reads and updates your window
		event, values = window.Read(timeout=100)

		update_image = False
		if event == None:
			print('None event')
			break
		elif event == '__TIMEOUT__':
			#print('TIMEOUT event')
			pass
		elif event == 'Quit':
			print('Quit event')
			break
		elif event == 'region_start':
			update_image = True
		elif event == 'region_end':
			update_image = True
		elif event == '_GRAPH_':
			(x,y) = values['_GRAPH_']
			x = (x-1)//4
			y = (y-1)//4
			print('you clicked at (graph) %d,%d' % (x,y))
			addr = xy2d(n, x,y) + lowest
			print('maps to %d (0x%X)' % (addr,addr))
			for start in addr2name:
				end = addr2end[start]
				if addr >= start and addr < end:
					name = addr2name[start]
					window.FindElement('_FUNCTION_').Update(value=name)
					window.FindElement('_START_').Update(value=hex(start))
					window.FindElement('_END_').Update(value=hex(end))
					# draw that
					img = img_background.copy()
					draw = ImageDraw.Draw(img)
					print('drawing %s [0x%04X, 0x%04X)' % (name, start, end))
					draw_region(start - lowest, end - lowest, '#FFFFFF', '#FF0000')
					graph.DrawImage(data=img_to_b64gif(img), location=(0,height-1))
					
		else:
			print('unknown event: ', event)
			print('       values: ', values)
			pass
		
		if initial_loop:
			graph.DrawImage(data=img_to_b64gif(img_background), location=(0,height-1))
			initial_loop = False

	window.Close() # Don't forget to close your window!
