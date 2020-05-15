#!/usr/bin/env python3

import os
import sys
import random
import socket

import binaryninja
from binaryninja.binaryview import BinaryViewType

from sfcurves.hilbert import forward, reverse, outline, generator
from palettes import to_pygame, viridis, plasma, inferno, cividis
from utils import function_span

palette_i = 0
palettes = [to_pygame(viridis), to_pygame(plasma), to_pygame(inferno), to_pygame(cividis)]

def draw_bytes(surface, data):
	global palettes, palette_i
	palette = palettes[palette_i]

	w = surface.get_width()

	surface.fill((0,0,0))
	px = pygame.PixelArray(surface)

	hgen = generator(length)
	for d in range(len(data)):
		(x,y) = next(hgen)
		px[x,w-1-y] = palette[data[d]]
	del px

if __name__ == '__main__':
	bv = BinaryViewType.get_view_of_file(sys.argv[1])
	bv.update_analysis_and_wait()

	# data is all segments concatenated
	data = b''
	segment2dd = {}
	for segment in sorted(bv.segments, key=lambda s: s.start):
		segment2dd[segment] = (len(data), len(data)+len(segment))
		data += bv.read(segment.start, len(segment))

	for seg in sorted(segment2dd, key=lambda s: segment2dd[s]):
		(d0, d1) = segment2dd[seg]
		print('segment %s is mapped to d=[0x%X, 0x%X)' % (seg, d0, d1))

	def d2addr(d):
		for seg in bv.segments:
			(d0,d1) = segment2dd[seg]
			if d>=d0 and d<d1:
				return seg.start + (d-d0)
		return None

	def addr2d(addr):
		seg = bv.get_segment_at(addr)
		if seg == None:
			return None
		(d0,d1) = segment2dd[seg]
		return d0 + (addr - seg.start)

	# calculate dimensions
	(width, length) = (2,4)
	while length < len(data):
		length *= 4
		width *= 2

	#
	func2outlines = {}
	for f in bv.functions:
		outlines = []
		for (a,b) in function_span(f):
			d0 = addr2d(a)
			d1 = addr2d(b)
			tmp = outline(d0, d1, length)
			tmp = [(x, width-y) for (x,y) in tmp] # cartesian -> pygame
			outlines.append(tmp)

		func2outlines[f] = outlines
		#if f.start == 0x140011990:
		#	sys.exit(-1)

	#--------------------------------------------------------------------------
	# pygame
	#--------------------------------------------------------------------------
	import pygame
	from pygame.locals import *
	pygame.init()
	surface_win = pygame.display.set_mode((width, width))
	pygame.display.set_caption('Hilbert Test')

	current_addr = 0

	# draw
	draw_bytes(surface_win, data)
	surface_bg = surface_win.copy()

	redraw = True
	while 1:
		redraw_region = False

		# process pygame events
		event = pygame.event.wait()
		if event.type == QUIT:
			pygame.quit()
			sys.exit()

		# change palette with 'a' and 'q' keys
		if event.type == KEYDOWN:
			if event.key == pygame.K_q:
				palette_i = (palette_i+1) % len(palettes)
				redraw = True
			elif event.key == pygame.K_a:
				palette_i = (palette_i-1) % len(palettes)
				redraw = True

			if redraw:
				draw_bytes(surface_bg, data)
				surface_win.blit(surface_bg, (0,0))
				redraw_region = True

		# mouse motion outlines regions and changes window title
		if event.type == MOUSEMOTION or redraw_region:
			redraw = True
			surface_win.blit(surface_bg, (0,0))

			(x,y) = pygame.mouse.get_pos() # to pygame coords
			#print('hovered: ', (x,y))
			(x,y) = (x, width-1-y) # to cartesian coords
			#print('cartesian: ', (x,y))
			d = reverse(x, y, length) # to 1-d hilbert coords
			#print('d: ', d)

			# map d back to an address by looking thru segments
			current_addr = d2addr(d)
			#print('addr: ', current_addr)

			functions = []
			if current_addr:
				functions = bv.get_functions_containing(current_addr)

			for f in functions:
				for outline in func2outlines[f]:
					pygame.draw.polygon(surface_win, (255,255,255), outline, 2)

		# mouse click navigates (relies on binja having udp nav plugin)
		if event.type == MOUSEBUTTONDOWN:
			if current_addr:
				addr = current_addr
				tmp = bv.get_functions_containing(current_addr)
				if tmp:
					addr = tmp[0].start

				sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
				print('navigating to 0x%X' % addr)
				message = hex(addr).encode('utf-8')
				sock.sendto(message, ('127.0.0.1', 31337))
				sock.close()

		if redraw:
			section = ''
			function = ''

			if current_addr != None:
				tmp = bv.get_sections_at(current_addr)
				if tmp: section = tmp[0].name

				tmp = bv.get_functions_containing(current_addr)
				if tmp: function = tmp[0].name
			else:
				current_addr = 0

			info = '[0x%X] [%s] [%s]' % (current_addr, section, function)
			pygame.display.set_caption(info)
			pygame.display.update()
			redraw = False
