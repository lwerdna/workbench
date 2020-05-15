#!/usr/bin/env python3

import os
import sys
import random
import socket

import binaryninja
from binaryninja.binaryview import BinaryViewType

from sfcurves.hilbert import forward, reverse, outline, generator
from palettes import to_pygame, viridis, plasma, inferno, cividis

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
	#--------------------------------------------------------------------------
	# get input data
	#--------------------------------------------------------------------------
	fpath = sys.argv[1]
	bv = BinaryViewType.get_view_of_file(fpath)
	bv.update_analysis_and_wait()

	# parse funcs, build regions
	funcs_hi = None
	regions = []
	for f in bv.functions:
		(n, s, e) = (f.symbol.full_name+'()', f.start, f.start+f.total_bytes)
		regions.append({'name':n, 'start':s, 'end':e})
	# data is all sections concatenated
	d = 0
	data = b''
	sections = []
	for name in sorted(bv.sections, key=lambda sname: bv.sections[sname].start):
		(s, e) = (bv.sections[name].start, bv.sections[name].end)
		sections.append({'name':name, 'start':s, 'end':e, 'd0':d, 'd1':d+e-s})
		data += bv.read(s, e-s)
		d += e-s
	base = sections[0]['start']
	# calculate dimensions
	(width, length) = (2,4)
	while length < len(data):
		length *= 4
		width *= 2
	# calculate region enclosures with length
	for r in regions:
		tmp = outline(r['start']-base, r['end']-1-base, length)
		r['enclosure'] = [(pt[0], width-1-pt[1]) for pt in tmp]

	#--------------------------------------------------------------------------
	# pygame
	#--------------------------------------------------------------------------
	import pygame
	from pygame.locals import *	
	pygame.init()
	surface_win = pygame.display.set_mode((width, width))
	pygame.display.set_caption('Hilbert Test')

	current_addr = 0
	current_func = ''
	current_section = ''

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
			(x,y) = (x, width-1-y) # to cartesian coords
			d = reverse(x, y, length) # to 1-d hilbert coords
			section = next((s for s in sections if d>=s['d0'] and d<s['d1']), None) # to section

			if section:
				current_section = section['name']
				current_addr = section['start'] + d - section['d0'] # to address
				current_region = next((r for r in regions if current_addr>=r['start'] and current_addr<r['end']), None)
				if current_region:
					current_func = current_region['name']
					current_addr = current_region['start'] # if clicked func, start there
					pygame.draw.polygon(surface_win, (255,255,255), current_region['enclosure'], 2)
				else:
					current_func = ''
			else:
				current_section = ''
				current_addr = 0

		# mouse click navigates (relies on binja having udp nav plugin)
		if event.type == MOUSEBUTTONDOWN:
			sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
			addr = current_addr
			if current_region:
				addr = current_region['start']
			message = hex(addr).encode('utf-8')
			sock.sendto(message, ('127.0.0.1', 31337))
			sock.close()

		if redraw:
			info = '[0x%X] [%s] [%s]' % (current_addr, current_section, current_func)
			pygame.display.set_caption(info)
			pygame.display.update()
			redraw = False
