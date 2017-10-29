#!/usr/bin/env python

import re
import math
import cairo
from PIL import Image

DEBUG = False

margin_x = 9
margin_y = 97

hex_r = 54.0
hex_outline_width = 1

save_ink = True

color_default = (1, 1, 1)
#color_default = (0, 0, 0)
#color_default = (.8, .8, .8)
color_black = (0, 0, 0)
color_white = (1, 1, 1)
color_red = (1, 0, 0)
color_green = (0, 0xcc/255.0, 0x66/255.0)
color_blue = (0x33/255.0, 0x66/255.0, 0xff/255.0)
color_yellow = (1, 1, 0)
color_magenta = (1, 0, 1)

color_city = (255, 255, 255)
#color_city = (0xf9/255.0, 0xC9/255.0, 0xC4/255.0)
color_industrial = (.3,.3,.3)
color_water = (0x0, 0xBf/255.0, 0xff)
color_plains = (0xfe/255.0, 0xfe/255.0, 0xe8/255.0)
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

# calculate width and height to meet target ratio
width_px = margin_x + hex_r + (n_hex_ew-1)*1.5*hex_r + hex_r + margin_x
height_px = margin_y + n_hex_ns * hex_h + margin_y+1
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
	x = margin_x + hex_r + x*1.5*hex_r
	y = margin_y + hex_rr + y*hex_rr
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
		lookup[key]['text'] = None
		lookup[key]['subtext'] = None
		lookup[key]['text_color'] = color_black

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

# 1/6 cities
cities = ['E1', 'L2', 'E3', 'H4', 'P4', 'D6', 'L6', 'R6', 'E9', 'I9', 'S9', \
  'O11', 'U11', 'B12', 'I13', 'U13', 'N14', 'A15', 'I15', 'U15', 'A17', \
  'G17', 'A19']
names = ['Chicago', 'Indianapolis', 'South Bend', 'Fort Wayne', 'Cincinnati', \
  'Toledo', 'Columbus', 'Ashland', 'Cleveland', 'Youngstown', 'Charleston', \
  'Clarksburg', 'Roanoake', 'Buffalo', 'Altoona', 'Lynchburg', 'Martinsburg', \
  'Syracuse', 'Harrisburg', 'Richmond', 'Ithaca', 'Binghampton', 'Albany']
subtext = ['3 - 7 - 7', '1 - 2 - 4', '2 - 1 - 3', '1 - 1 - 3', '2 - 2 - 4', '2 - 1 - 2', '1 - 1 - 2', '2 - 2 - 3', '1 - 2 - 4', '2 - 1 - 2', '3 - 2 - 3', '2 - 1 - 2', '2 - 1 - 2', '2 - 3 - 5', '2 - 1 - 2', '1 - 1 - 2', '2 - 1 - 2', '2 - 1 - 3', '2 - 1 - 2', '2 - 2 - 3', '2 - 1 - 2', '2 - 1 - 2', '2 - 1 - 3']
for i in range(len(cities)):
	lookup[cities[i]]['text'] = names[i]
	lookup[cities[i]]['fill'] = color_city
	lookup[cities[i]]['subtext'] = subtext[i]
lookup['H4']['fill'] = color_magenta

# 2/6 start
lookup['G19']['text'] = 'NY Central'
lookup['G19']['fill'] = color_green
lookup['L18']['text'] = 'Pennsylvania'
lookup['L18']['fill'] = color_red
lookup['O17']['text'] = 'Balt. & Ohio'
lookup['O17']['fill'] = color_blue
lookup['S17']['text'] = 'Ches. & Ohio'
lookup['S17']['fill'] = color_yellow

# 3/6 industrial
industrials = ['A5', 'I11', 'M9']
names = ['Detroit', 'Pittsburgh', 'Wheeling']
subtext = ['1', '4', '3']
for i,key in enumerate(industrials):
	lookup[key]['text'] = names[i]
	lookup[key]['fill'] = color_industrial
	lookup[key]['subtext'] = subtext[i]
	lookup[key]['text_color'] = color_white

# 4/6 mountains
mountains = 'S7 T8 Q9 U9 N10 P10 R10 T10 M11 Q11 J12 L12 N12 K13 M13 J14'.split()
costs = [3, 3, 4, 3, 3, 4, 4, 3, 4, 4, 3, 4, 2, 4, 2, 3]
assert len(mountains) == len(costs)
for i,key in enumerate(mountains):
	lookup[key]['subtext'] = str(costs[i])
	lookup[key]['fill'] = color_mountain

# 5/6 forest
forests = 'Q7 P8 R8 K9 O9 F10 H10 J10 L10 E11 G11 K11 S11 F12 H12 P12 R12 C13 E13 G13 O13 Q13 S13 D14 F14 H14 L14 P14 C15 E15 G15 S15 D16 F16 H16 C17 E17 I17 D18 F18 H18'.split()
costs = [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 2, 2, 3, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2, 4, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
assert(len(forests) == len(costs))
for i,key in enumerate(forests):
	lookup[key]['subtext'] = str(costs[i])
	lookup[key]['fill'] = color_forest

# 6/6 plains (all plains have cost 1)
for x in 'G1 I1 F2 H2 J2 N2 A3 C3 G3 I3 K3 M3 O3 B4 D4 F4 J4 L4 N4 C5 E5 G5 I5 K5 M5 O5 Q5 F6 H6 J6 N6 P6 E7 G7 I7 K7 M7 O7 F8 H8 J8 L8 N8 G9 D10 C11 D12 A13 B14 B16 B18 C19 E19 I19 K19 J18 K17 M17 Q17 J16 L16 N16 P16 R16 T16 K15 M15 O15 Q15 R14 T14 T12'.split():
	lookup[x]['subtext'] = '1'
	lookup[x]['fill'] = color_plains

###############################################################################
# funcs
###############################################################################

def drawRect(cr, x, y, width, height, color):
	cr.set_source_rgb(*color)
	cr.rectangle(x, y, width, height)
	cr.fill()	

def drawCrossHatch(cr, x, y, width, height, color):
	cr.set_source_rgb(*color_white)
	cr.rectangle(x, y, width, height)
	cr.fill()

	cr.save()
	cr.rectangle(x, y, width, height)
	cr.clip()
	cr.new_path()
	cr.set_source_rgb(*color)
	cr.set_line_width(.5)

	start = int(x - height)
	end = int(x + width + height)

	for k in xrange(start, end, 12):
		cr.move_to(k, y)
		cr.line_to(k + height, y+height)
		cr.move_to(k, y+height)
		cr.line_to(k+height, y)
	cr.stroke()
	cr.restore()

def write(message, color, x, y, font='Georgia', size=15, backdrop=None):

	cr.select_font_face(font)
	cr.set_font_size(size)

	(x_bear, y_bear, width, height, x_advance, y_advance) = cr.text_extents(message)


	pos_x = x - width/2
	pos_y = y + height/2

	if backdrop:
		cr.set_source_rgb(*backdrop)
		cr.rectangle(pos_x-4, pos_y-height-4, width+8, height+8)
		cr.fill()

	cr.set_source_rgb(*color)
	cr.move_to(pos_x, pos_y)
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

	cr.set_line_width(hex_outline_width)
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

	text_color = lookup[key]['text_color']

	if DEBUG:
		write(key, text_color, x, y + hex_rr-12)

	if lookup[key]['text']:
		write(lookup[key]['text'], text_color, x, y)

	if lookup[key]['subtext']:
		write(lookup[key]['subtext'], text_color, x, y-hex_rr + 8)

###############################################################################
# main
###############################################################################

surface = cairo.ImageSurface(cairo.FORMAT_RGB24, width_px, height_px)
cr = cairo.Context(surface)

# default white background
drawRect(cr, 0, 0, width_px, height_px, color_white)

# default back
posA = key2pos('A1')
posB = key2pos('U19')
if save_ink:
	drawCrossHatch(cr, posA[0]-hex_r, posA[1]-hex_rr, posB[0]-posA[0]+hex_w, posB[1]-posA[1]+hex_h, color_black)
else:
	drawRect(cr, posA[0]-hex_r, posA[1]-hex_rr, posB[0]-posA[0]+hex_w, posB[1]-posA[1]+hex_h, color_black)

# draw Michigan
posA = key2pos('A1')
posB = key2pos('E3')
if save_ink:
	drawCrossHatch(cr, posA[0]-hex_r, posA[1]-hex_rr, posB[0]-posA[0]+hex_r, posB[1]-posA[1]+hex_rr, color_water)
else:
	drawRect(cr, posA[0]-hex_r, posA[1]-hex_rr, posB[0]-posA[0]+hex_r, posB[1]-posA[1]+hex_rr, color_water)
pos = key2pos('B1')
write('Michigan', color_black, pos[0], pos[1], 'Georgia', 18, color_white)

# draw Erie
posA = key2pos('A5')
posB = key2pos('F13')
width = posB[0]-posA[0]
height = posB[1]-posA[1]
if save_ink:
	drawCrossHatch(cr, posA[0], posA[1]-hex_rr, width, height+hex_rr, color_water)
else:
	drawRect(cr, posA[0], posA[1]-hex_rr, width, height+hex_rr, color_water)
pos = key2pos('B8')
write('Erie', color_black, pos[0], pos[1], 'Georgia', 18, color_white)

# draw Atlantic
posA = key2pos('G15')
posB = key2pos('U19')
if save_ink:
	drawCrossHatch(cr, posA[0], posA[1], posB[0]-posA[0]+hex_r, posB[1]-posA[1]+hex_rr, color_water)
else:
	drawRect(cr, posA[0], posA[1], posB[0]-posA[0]+hex_r, posB[1]-posA[1]+hex_rr, color_water)
pos = key2pos('R19')
write('Atlantic', color_black, pos[0], pos[1], 'Georgia', 18, color_white)

for x in range(19):
	for y in range(21):
		if x%2 != y%2:
			continue
		key = coords2key(x,y)
		if lookup[key]['visible'] == False:
			continue
		drawHex_KEY(cr, key)

cr.set_source_rgb(*color_black)
cr.set_line_width(2)
cr.rectangle(0,0,width_px,height_px)
cr.stroke()

if DEBUG:
	write('final image size: %dx%d (ratio:%f)' % \
	  (width_px, height_px, 1.0*width_px/height_px), color_black, 128, 32)

surface.write_to_png("/tmp/quick.png")
