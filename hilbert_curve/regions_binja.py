#!/usr/bin/env python

# draw functions (identified with Binary Ninja) as Hilbert curve regions
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

	if False:
		# "simpson's colors" solid each function regions

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
	else:
		# color-coded bytes, white outlined function regions
		# viridis from matplotlib
		palette = [
		'#440154', '#440255', '#440357', '#450558', '#45065A', '#45085B',
		'#46095C', '#460B5E', '#460C5F', '#460E61', '#470F62', '#471163',
		'#471265', '#471466', '#471567', '#471669', '#47186A', '#48196B',
		'#481A6C', '#481C6E', '#481D6F', '#481E70', '#482071', '#482172',
		'#482273', '#482374', '#472575', '#472676', '#472777', '#472878',
		'#472A79', '#472B7A', '#472C7B', '#462D7C', '#462F7C', '#46307D',
		'#46317E', '#45327F', '#45347F', '#453580', '#453681', '#443781',
		'#443982', '#433A83', '#433B83', '#433C84', '#423D84', '#423E85',
		'#424085', '#414186', '#414286', '#404387', '#404487', '#3F4587',
		'#3F4788', '#3E4888', '#3E4989', '#3D4A89', '#3D4B89', '#3D4C89',
		'#3C4D8A', '#3C4E8A', '#3B508A', '#3B518A', '#3A528B', '#3A538B',
		'#39548B', '#39558B', '#38568B', '#38578C', '#37588C', '#37598C',
		'#365A8C', '#365B8C', '#355C8C', '#355D8C', '#345E8D', '#345F8D',
		'#33608D', '#33618D', '#32628D', '#32638D', '#31648D', '#31658D',
		'#31668D', '#30678D', '#30688D', '#2F698D', '#2F6A8D', '#2E6B8E',
		'#2E6C8E', '#2E6D8E', '#2D6E8E', '#2D6F8E', '#2C708E', '#2C718E',
		'#2C728E', '#2B738E', '#2B748E', '#2A758E', '#2A768E', '#2A778E',
		'#29788E', '#29798E', '#287A8E', '#287A8E', '#287B8E', '#277C8E',
		'#277D8E', '#277E8E', '#267F8E', '#26808E', '#26818E', '#25828E',
		'#25838D', '#24848D', '#24858D', '#24868D', '#23878D', '#23888D',
		'#23898D', '#22898D', '#228A8D', '#228B8D', '#218C8D', '#218D8C',
		'#218E8C', '#208F8C', '#20908C', '#20918C', '#1F928C', '#1F938B',
		'#1F948B', '#1F958B', '#1F968B', '#1E978A', '#1E988A', '#1E998A',
		'#1E998A', '#1E9A89', '#1E9B89', '#1E9C89', '#1E9D88', '#1E9E88',
		'#1E9F88', '#1EA087', '#1FA187', '#1FA286', '#1FA386', '#20A485',
		'#20A585', '#21A685', '#21A784', '#22A784', '#23A883', '#23A982',
		'#24AA82', '#25AB81', '#26AC81', '#27AD80', '#28AE7F', '#29AF7F',
		'#2AB07E', '#2BB17D', '#2CB17D', '#2EB27C', '#2FB37B', '#30B47A',
		'#32B57A', '#33B679', '#35B778', '#36B877', '#38B976', '#39B976',
		'#3BBA75', '#3DBB74', '#3EBC73', '#40BD72', '#42BE71', '#44BE70',
		'#45BF6F', '#47C06E', '#49C16D', '#4BC26C', '#4DC26B', '#4FC369',
		'#51C468', '#53C567', '#55C666', '#57C665', '#59C764', '#5BC862',
		'#5EC961', '#60C960', '#62CA5F', '#64CB5D', '#67CC5C', '#69CC5B',
		'#6BCD59', '#6DCE58', '#70CE56', '#72CF55', '#74D054', '#77D052',
		'#79D151', '#7CD24F', '#7ED24E', '#81D34C', '#83D34B', '#86D449',
		'#88D547', '#8BD546', '#8DD644', '#90D643', '#92D741', '#95D73F',
		'#97D83E', '#9AD83C', '#9DD93A', '#9FD938', '#A2DA37', '#A5DA35',
		'#A7DB33', '#AADB32', '#ADDC30', '#AFDC2E', '#B2DD2C', '#B5DD2B',
		'#B7DD29', '#BADE27', '#BDDE26', '#BFDF24', '#C2DF22', '#C5DF21',
		'#C7E01F', '#CAE01E', '#CDE01D', '#CFE11C', '#D2E11B', '#D4E11A',
		'#D7E219', '#DAE218', '#DCE218', '#DFE318', '#E1E318', '#E4E318',
		'#E7E419', '#E9E419', '#ECE41A', '#EEE51B', '#F1E51C', '#F3E51E',
		'#F6E61F', '#F8E621', '#FAE622', '#FDE724'
		]

		for d in range(0, n**2):
			(x,y) = d2xy(n, d)
			byte = bv.read(lowest+d, 1)
			color = palette[byte[0]] if byte else '#000000'
			draw.point((x,y), fill=color)

		for a in addr2name:
			addr_start = a
			addr_end = addr2end[a]

			if addr_end - addr_start < 4:
				continue

			print('drawing %s [0x%04X, 0x%04X)' % (addr2name[a], addr_start, addr_end))
			draw_region(addr_start - lowest, addr_end - lowest, '#000000', None)

	del draw
	fpath = '/tmp/tmp.png'
	print('saving %s' % fpath)
	img.save(fpath)
