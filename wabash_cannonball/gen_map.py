#!/usr/bin/env python

import re
import math
import cairo
from PIL import Image

margin = 8
	
hex_r = 32.0

color_default = (.8, .8, .8)
color_black = (0, 0, 0)
color_white = (1, 1, 1)

color_city = (0xf9/255.0, 0x99/255.0, 0x94/255.0)
color_industrial = (.3,.3,.3)
color_water = (0xF0/255.0, 1, 1)
color_plains = (0xfe/255.0, 0xfe/255.0, 0xc8/255.0)
color_forest = (0xd5/255.0, 0xf5/255.0, 0xd5/255.0)
color_mountain = (0x8c/255.0, 0x84/255.0, 0x7f/255.0)

###############################################################################
# measuring, coordinates
###############################################################################


hex_w = 2.0*hex_r

hex_h = math.sqrt(3)*hex_r
hex_rr = hex_h/2

n_hex_ew = 19
n_hex_ns = 11

width_px = margin + hex_r + (n_hex_ew-1)*1.5*hex_r + hex_r + margin
height_px = margin + n_hex_ns * hex_h + margin

[width_px, height_px] = map(int, map(math.ceil, [width_px, height_px]))

# eg: 'A1' -> [0,0] (map coordinates)
def key2coords(key):
	m = re.match(r'^([A-Z]+)(\d+)$', key)
	(let, num) = m.group(1,2)
	y = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.index(let)
	x = int(num)-1
	return [x,y]

# eg: 'A1' -> [35,35] (cairo surface position)
def key2pos(key):
	[x,y] = key2coords(key)
	return coords2pos(x,y)

# eg: (0,0) -> [35,35] (cairo surface position)
def coords2pos(x,y):
	x = margin + hex_r + x*1.5*hex_r
	y = margin + hex_rr + y*hex_rr
	return [x,y]

# eg: (0,0) -> 'A1'
def coords2key(x,y):
	return 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'[y] + str(x+1)


###############################################################################
# global hex data
###############################################################################

lookup = {}
for x in range(19):
	for y in range(21):
		key = coords2key(x,y)
		lookup[key] = {}
		lookup[key]['visible'] = True
		lookup[key]['fill'] = color_white
		lookup[key]['stroke'] = color_black
		lookup[key]['text'] = ''

# remove Lake Michigan
blanks = ['A1', 'B2', 'C1', 'D2' ]
# remove Lake Erie
blanks += ['B6', 'A7', 'C7', 'B8', 'D8', 'A9', 'C9', 'B10', 'A11']
# bottom left
blanks += ['K1', 'M1', 'O1', 'Q1', 'S1', 'U1', 'P2', 'R2', 'T2']
blanks += ['Q3', 'S3', 'U3', 'R4', 'T4', 'S5', 'U5', 'T6', 'U7']
# Atlantic Ocean
blanks += ['M19', 'O19', 'Q19', 'S19', 'U19', 'N18', 'P18', 'R18', 'T18', 'U17']
for k in blanks:
	lookup[k]['visible'] = False

# wheeling, pittsburg, detroit
lookup['A5']['text'] = 'Wheeling'
lookup['A5']['fill'] = color_industrial
lookup['I11']['text'] = 'Pittsburg'
lookup['I11']['fill'] = color_industrial
lookup['M9']['text'] = 'Detroit'
lookup['M9']['fill'] = color_industrial

# cities
cities = ['E1', 'L2', 'E3', 'H4', 'P4', 'D6', 'L6', 'R6', 'E9', 'I9', 'S9', \
  'O11', 'U11', 'B12', 'I13', 'U13', 'N14', 'A15', 'I15', 'U15', 'A17', \
  'G17', 'A19']
names = ['Chicago', 'Indianapolis', 'South Bend', 'Fort Wayne', 'Cincinnati', \
  'Toledo', 'Columbus', 'Ashland', 'Cleveland', 'Youngstown', 'Charleston', \
  'Clarksburg', 'Roanoake', 'Buffalo', 'Altoona', 'Lynchburg', 'Martinsburg', \
  'Syracuse', 'Harrisburg', 'Richmond', 'Ithaca', 'Binghampton', 'Albany']
for i in range(len(cities)):
	lookup[cities[i]]['text'] = names[i]
	lookup[cities[i]]['fill'] = color_city

# plains
for x in 'G1 I1 F2 H2 J2 N2 A3 C3 G3 I3 K3 M3 O3 B4 D4 F4 J4 L4 N4 C5 E5 G5 I5 K5 M5 O5 Q5 F6 H6 J6 N6 P6 E7 G7 I7 K7 M7 O7 F8 H8 J8 L8 N8 G9 D10 C11 D12 A13 B14 B16 B18 C19 E19 I19 K19 J18 K17 M17 Q17 J16 L16 N16 P16 R16 T16 K15 M15 O15 Q15 R14 T14 T12'.split():
	lookup[x]['fill'] = color_plains

# 
for x in 'Q7 P8 O9 R8 K9 L10 K11 J10 H10 F10 E11 G11 F12 H12 C13 E13 G13 D14 F14 H14 C15 E15 G15 D16 F16 H16 C17 E17 I17 D18 F18 H18 L14 P14 O13 Q13 S13 P12 R12 S11 S15'.split():
	lookup[x]['fill'] = color_forest

for x in 'J12 J14 K13 L12 M13 N12 M11 N10 P10 Q11 R10 Q9 T10 U9 T8 S7'.split():
	lookup[x]['fill'] = color_mountain

###############################################################################
# funcs
###############################################################################

def write(message, color, x, y):
	cr.set_source_rgb(*color)
	cr.move_to(x, y)
	cr.show_text(message)

# eg: (0xFF, 0, 0) -> (1.0, 0, 0)
def hexRgb(r,g,b):
	return (r/255.0, g/255.0, b/255.0)

def drawHex_KEY(cr, key):
	[x,y] = key2coords(key)
	print '%s -> (%d,%d)' % (key, x, y),
	[x,y] = coords2pos(x,y)
	print '-> (%d,%d)' % (x, y)

	ratio = math.sqrt(3)/2.0

	cr.set_line_width(1)
	cr.set_source_rgb(*lookup[key]['stroke'])

	cr.move_to(x + hex_r, y)
	cr.line_to(x + hex_r/2.0, y - ratio*hex_r)
	cr.line_to(x - hex_r/2.0, y - ratio*hex_r)
	cr.line_to(x - hex_r, y)
	cr.line_to(x - hex_r/2.0, y + ratio*hex_r)
	cr.line_to(x + hex_r/2.0, y + ratio*hex_r)
	cr.line_to(x + hex_r, y)
	cr.stroke_preserve()

	cr.set_source_rgb(*lookup[key]['fill'])
	cr.fill()

	text_color = color_black
	if lookup[key]['fill'] == color_black:
		text_color = color_white	

	if lookup[key]['text']:
		write(lookup[key]['text'], text_color, x, y)
	else:
		write(key, text_color, x, y)

###############################################################################
# main
###############################################################################

surface = cairo.ImageSurface(cairo.FORMAT_RGB24, width_px, height_px)
cr = cairo.Context(surface)

# default white background
cr.set_source_rgb(*color_default)
cr.rectangle(0,0,width_px,height_px)
cr.fill()

# draw Michigan
cr.set_source_rgb(*color_water)
cr.rectangle(0,0, *key2pos('E3'))
cr.fill()
write('Lake\nMichigan', color_black, *key2pos('B1'))

# draw Erie
posA = key2pos('A5')
posB = key2pos('E13')
cr.set_source_rgb(*color_water)
cr.rectangle(posA[0], 0, posB[0]-posA[0], posB[1])
cr.fill()
write('Lake\nErie', color_black, *key2pos('A7'))
# draw Atlantic
posA = key2pos('G15')
cr.set_source_rgb(*color_water)
cr.rectangle(posA[0], posA[1], width_px-posA[0], height_px-posA[1])
cr.fill()
write('Atlantic\nOcean', color_black, *key2pos('P18'))

for x in range(19):
	for y in range(21):
		if x%2 != y%2:
			continue
		key = coords2key(x,y)
		if lookup[key]['visible'] == False:
			continue
		drawHex_KEY(cr, key)


#drawHex(cr, 512, 512)

#drawHex(cr, 512, 512)

 
surface.write_to_png("/tmp/quick.png")
