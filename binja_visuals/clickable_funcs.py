#!/usr/bin/env python

# display functions identified with BinaryNinja in a PySimpleGui interface

import io
import sys
import base64
from PIL import Image, ImageDraw
import binaryninja
from binaryninja.binaryview import BinaryViewType
from sfcurves.hilbert import forward, reverse, outline
import PySimpleGUI as sg

from utils import function_span

# globals
length = None
draw = None
width = None

def draw_region(start, stop, color1=None, color2=None):
	global length, draw
	trace = outline(start, stop, length)
	#trace = list(map(lambda p: (4*p[0]+1, width - (4*p[1]+1)), trace))
	trace = list(map(lambda p: (p[0], width - p[1]), trace))
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

	bv = BinaryViewType.get_view_of_file(fpath)
	bv.update_analysis_and_wait()

	func2span = {}
	(lowest, highest) = (bv.end, bv.start)
	for f in bv.functions:
		span = function_span(f)
		lowest = min(lowest, span[0][0])
		highest = max(highest, span[-1][1])
		func2span[f] = span
	print('lowest addr: 0x%X' % lowest)
	print('highest addr: 0x%X' % highest)

	width = 2
	length = 4
	while length < (highest-lowest):
		width *= 2
		length *= 4

	# generate background PIL image
	img_background = Image.new('RGB', (width, width))
	draw = ImageDraw.Draw(img_background)
	for f in bv.functions:
		for (lo,hi) in function_span(f):
			draw_region(lo-lowest, hi-lowest, '#FFFFFF')
	del draw
	print('total %d functions' % len(bv.functions))
	print('total %d blocks' % sum([len(f.basic_blocks) for f in bv.functions]))

	# start
	graph = sg.Graph((width,width), (0,0), (width-1, width-1), key='_GRAPH_', pad=(0,0), enable_events=True)
	gui_rows = [
				[graph],
				[sg.Text('function:'), sg.InputText('dummy', do_not_clear=True, key='_FUNCTION_')],
				[sg.Text('start:'), sg.InputText('00000000', do_not_clear=True, key='_START_')],
				[sg.Quit()]
			]

	window = sg.Window('Hilbert Curve Region', auto_size_text=True,  font='AndaleMono 16').Layout(gui_rows)

	initial_loop = True
	while (True):
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
			#x = (x-1)//4
			#y = (y-1)//4
			addr = reverse(x, y, length) + lowest
			print('click (%d,%d) -> 0x%X' % (x, y, addr))
			funcs = bv.get_functions_containing(addr)
			for f in funcs:
				print('drawing %d blocks from %s' % (len(f.basic_blocks), f.name))
				window['_FUNCTION_'].Update(value=f.name)
				window['_START_'].Update(value=hex(f.start))
				# draw all basic blocks
				img = img_background.copy()
				draw = ImageDraw.Draw(img)
				for (a,b) in func2span[f]:
					draw_region(a-lowest, b-lowest, '#FFFFFF', '#FF0000')
			graph.erase()
			graph.DrawImage(data=img_to_b64gif(img), location=(0,width-1))
					
		else:
			print('unknown event: ', event)
			print('       values: ', values)
			pass
		
		if initial_loop:
			graph.erase()
			graph.DrawImage(data=img_to_b64gif(img_background), location=(0,width-1))
			initial_loop = False

	window.Close() # Don't forget to close your window!
