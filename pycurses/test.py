#!/usr/bin/env python

import time
import curses

stdscr = None

def cursesMain(initwin):
	global stdscr
	stdscr = initwin
	(maxy,maxx) = stdscr.getmaxyx()

	curses.use_default_colors()

	curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)
 
	# try [0,255]

	for group in range(8):
		for y in range(32):
			x = group * 8
			asciiCode = y + group * 32
			try:
				stdscr.addstr(y,x,'%02X:'%asciiCode)
				stdscr.addch(y,x+3,asciiCode)
			except:
				pass

	stdscr.refresh()
	stdscr.getch()

	# do those special characters

	names = [ 'ACS_BBSS', 'ACS_BLOCK', 'ACS_BOARD', 'ACS_BSBS',
		'ACS_BSSB', 'ACS_BSSS', 'ACS_BTEE', 'ACS_BULLET', 'ACS_CKBOARD',
		'ACS_DARROW', 'ACS_DEGREE', 'ACS_DIAMOND', 'ACS_GEQUAL', 'ACS_HLINE',
		'ACS_LANTERN', 'ACS_LARROW', 'ACS_LEQUAL', 'ACS_LLCORNER', 'ACS_LRCORNER',
		'ACS_LTEE', 'ACS_NEQUAL', 'ACS_PI', 'ACS_PLMINUS', 'ACS_PLUS',
		'ACS_RARROW', 'ACS_RTEE', 'ACS_S1', 'ACS_S3', 'ACS_S7',
		'ACS_S9', 'ACS_SBBS', 'ACS_SBSB', 'ACS_SBSS', 'ACS_SSBB',
		'ACS_SSBS', 'ACS_SSSB', 'ACS_SSSS', 'ACS_STERLING', 'ACS_TTEE',
		'ACS_UARROW', 'ACS_ULCORNER', 'ACS_URCORNER', 'ACS_VLINE'
	]

	values = [ curses.ACS_BBSS, curses.ACS_BLOCK, curses.ACS_BOARD, curses.ACS_BSBS, curses.ACS_BSSB, curses.ACS_BSSS, curses.ACS_BTEE, curses.ACS_BULLET, curses.ACS_CKBOARD, curses.ACS_DARROW, curses.ACS_DEGREE, curses.ACS_DIAMOND, curses.ACS_GEQUAL, curses.ACS_HLINE, curses.ACS_LANTERN, curses.ACS_LARROW, curses.ACS_LEQUAL, curses.ACS_LLCORNER, curses.ACS_LRCORNER, curses.ACS_LTEE, curses.ACS_NEQUAL, curses.ACS_PI, curses.ACS_PLMINUS, curses.ACS_PLUS, curses.ACS_RARROW, curses.ACS_RTEE, curses.ACS_S1, curses.ACS_S3, curses.ACS_S7, curses.ACS_S9, curses.ACS_SBBS, curses.ACS_SBSB, curses.ACS_SBSS, curses.ACS_SSBB, curses.ACS_SSBS, curses.ACS_SSSB, curses.ACS_SSSS, curses.ACS_STERLING, curses.ACS_TTEE, curses.ACS_UARROW, curses.ACS_ULCORNER, curses.ACS_URCORNER, curses.ACS_VLINE]

	stdscr.erase()

	for i in range(len(names)):
		try:
			x = 0
			y = i
			stdscr.addstr(y,x,'%s:'%names[i], curses.color_pair(1))
			stdscr.addch(y,x+16,values[i])
		except:
			pass

	stdscr.refresh()
	stdscr.getch()

	color_lookup = [ \
		0x772277, 0x752277, 0x732277, 0x722378, 0x702378, 0x6F2378, 0x6D2479, 0x6B2479, \
		0x6A257A, 0x68257A, 0x67257A, 0x65267B, 0x64267B, 0x62277C, 0x60277C, 0x5F277C, \
		0x5D287D, 0x5C287D, 0x5A297E, 0x58297E, 0x57297E, 0x552A7F, 0x542A7F, 0x522B80, \
		0x512B80, 0x4F2B80, 0x4D2C81, 0x4C2C81, 0x4A2D82, 0x492D82, 0x472D82, 0x452E83, \
		0x442E83, 0x422F84, 0x412F84, 0x3F2F84, 0x3E3085, 0x3C3085, 0x3A3186, 0x393186, \
		0x373186, 0x363287, 0x343287, 0x333388, 0x323388, 0x313389, 0x30348A, 0x2F348B, \
		0x2F348B, 0x2E358C, 0x2D358D, 0x2C368E, 0x2B368F, 0x2B368F, 0x2A3790, 0x293791, \
		0x283892, 0x273893, 0x273893, 0x263994, 0x253995, 0x243A96, 0x233A97, 0x233A97, \
		0x223B98, 0x213B99, 0x203C9A, 0x203C9A, 0x1F3C9B, 0x1E3D9C, 0x1D3D9D, 0x1C3E9E, \
		0x1C3E9E, 0x1B3E9F, 0x1A3FA0, 0x193FA1, 0x1840A2, 0x1840A2, 0x1740A3, 0x1641A4, \
		0x1541A5, 0x1442A6, 0x1442A6, 0x1342A7, 0x1243A8, 0x1143A9, 0x1144AA, 0x1246A6, \
		0x1448A2, 0x154B9F, 0x174D9B, 0x184F98, 0x1A5294, 0x1C5491, 0x1D568D, 0x1F5989, \
		0x205B86, 0x225E82, 0x23607F, 0x25627B, 0x276578, 0x286774, 0x2A6971, 0x2B6C6D, \
		0x2D6E69, 0x2F7166, 0x307362, 0x32755F, 0x33785B, 0x357A58, 0x367C54, 0x387F51, \
		0x3A814D, 0x3B8449, 0x3D8646, 0x3E8842, 0x408B3F, 0x428D3B, 0x438F38, 0x459234, \
		0x469431, 0x48972D, 0x499929, 0x4B9B26, 0x4D9E22, 0x4EA01F, 0x50A21B, 0x51A518, \
		0x53A714, 0x55AA11, 0x58A510, 0x5CA110, 0x609D0F, 0x64990F, 0x67950E, 0x6B910E, \
		0x6F8D0E, 0x73890D, 0x77850D, 0x7A810C, 0x7E7D0C, 0x82790C, 0x86750B, 0x8A710B, \
		0x8D6D0A, 0x91690A, 0x95650A, 0x996109, 0x9C5D09, 0xA05908, 0xA45508, 0xA85008, \
		0xAC4C07, 0xAF4807, 0xB34406, 0xB74006, 0xBB3C06, 0xBF3805, 0xC23405, 0xC63004, \
		0xCA2C04, 0xCE2804, 0xD12403, 0xD52003, 0xD91C02, 0xDD1802, 0xE11402, 0xE41001, \
		0xE80C01, 0xEC0800, 0xF00400, 0xF40000, 0xF40500, 0xF40A00, 0xF41001, 0xF51501, \
		0xF51B02, 0xF52002, 0xF52503, 0xF62B03, 0xF63004, 0xF63604, 0xF63B05, 0xF74005, \
		0xF74606, 0xF74B06, 0xF75107, 0xF85607, 0xF85B08, 0xF86108, 0xF86609, 0xF96C09, \
		0xF9710A, 0xF9760A, 0xFA7C0A, 0xFA810B, 0xFA870B, 0xFA8C0C, 0xFB910C, 0xFB970D, \
		0xFB9C0D, 0xFBA20E, 0xFCA70E, 0xFCAC0F, 0xFCB20F, 0xFCB710, 0xFDBD10, 0xFDC211, \
		0xFDC711, 0xFDCD12, 0xFED212, 0xFED813, 0xFEDD13, 0xFFE314, 0xFEE319, 0xFEE41F, \
		0xFEE524, 0xFEE52A, 0xFEE62F, 0xFEE735, 0xFEE73B, 0xFEE840, 0xFEE946, 0xFEE94B, \
		0xFEEA51, 0xFEEB57, 0xFEEB5C, 0xFEEC62, 0xFEED67, 0xFEED6D, 0xFEEE73, 0xFEEF78, \
		0xFEEF7E, 0xFEF083, 0xFEF189, 0xFEF18F, 0xFEF294, 0xFEF39A, 0xFEF39F, 0xFEF4A5, \
		0xFEF5AB, 0xFEF5B0, 0xFEF6B6, 0xFEF7BB, 0xFEF7C1, 0xFEF8C7, 0xFEF9CC, 0xFEF9D2, \
		0xFEFAD7, 0xFEFBDD, 0xFEFBE3, 0xFEFCE8, 0xFEFDEE, 0xFEFDF3, 0xFEFEF9, 0xFEFFFF
	]

	for c in range(8):
		r = color_lookup[c] >> 16
		g = (color_lookup[c] & 0xFF00) >> 8
		b = color_lookup[c] & 0xFF
		stdscr.addstr(0,0,"trying to make color %d be %02X %02X %02X" % (c+1, r, g, b), curses.color_pair(1))
		try:
			curses.init_color(c+1, r, g, b)
		except:
			pass

	stdscr.erase()

	for x in range(8):
		for y in range(8):
			try:
				stdscr.addchr(x, y, curses.ACS_CKBOARD, curses.color_pair(8*x+y+1))
			except:
				pass

	stdscr.refresh()
	stdscr.getch()


#	for i in range(32):
#		stdscr.addch(1 + i+32, 2, i+32)
#	for i in range(32):
#		stdscr.addch(1 + i+64, 4, i+64)
#	for i in range(32):
#		stdscr.addch(1 + i+96, 6, i+96)

#	i = 2
#	while 1:
#		stdscr.addstr(0, 0,"trying to init_pair(%d)"%i, curses.color_pair(1))
#		#curses.init_pair(i, curses.COLOR_RED, curses.COLOR_WHITE)
#		stdscr.refresh()
#		i += 1

	stdscr.getch()

if __name__ == '__main__':
	curses.wrapper(cursesMain)


