#!/usr/bin/env python

import time
import curses

stdscr = None

def cursesMain(initwin):
	global stdscr
	stdscr = initwin
	(maxy,maxx) = stdscr.getmaxyx()

	# necessary for init_pair()
	curses.use_default_colors()

	try:
		# returns 256, 32767 on MacOS
		stdscr.addstr(0,0,'')
		stdscr.addstr('curses.COLORS: %d\n' % curses.COLORS)
		stdscr.addstr('curses.COLOR_PAIRS: %d\n' % curses.COLOR_PAIRS)
		# initially pair 0 is (fg,bg)=(7,0) or white-on-black
		# all others are (0,0) or black-on-black
		for i in range(16):
			(fg,bg) = curses.pair_content(i)
			stdscr.addstr('pair %d has (fg,bg)=(%d,%d)\n' % (i,fg,bg))

		for i in range(curses.COLORS):
			curses.init_pair(i+1, i, -1)
			stdscr.addch(curses.ACS_CKBOARD, curses.color_pair(i+1))

#		for i in range(10):
#			stdscr.addstr('X', curses.color_pair(i))	
	
		stdscr.refresh()
		stdscr.getch()
	except curses.error as e:
		print e
	
#	for y in range(8):
#		for x in range(8):
#			stdscr.addch(y,x,
	
#	curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)
# 
#	# try [0,255]
#
#	for group in range(8):
#		for y in range(32):
#			x = group * 8
#			asciiCode = y + group * 32
#			try:
#				stdscr.addstr(y,x,'%02X:'%asciiCode)
#				stdscr.addch(y,x+3,asciiCode)
#			except:
#				pass
#
#	stdscr.refresh()
#	stdscr.getch()



if __name__ == '__main__':
	curses.wrapper(cursesMain)


