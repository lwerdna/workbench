#!/usr/bin/env python

import curses

stdscr = None

def get_param(prompt_string):
	global stdscr
	stdscr.clear()
	stdscr.border(0)
	stdscr.addstr(2, 2, prompt_string)
	stdscr.refresh()
	curses.echo()
	input = stdscr.getstr(10, 10, 60)
	curses.noecho()
	return input

def cursesMain(initwin):
	global stdscr
	stdscr = initwin
	(maxy,maxx) = stdscr.getmaxyx()

	stdscr.border()

	curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)

	stdscr.addstr(0,0, "A", curses.color_pair(1))
	stdscr.addstr(0,maxx-1, "B", curses.color_pair(1))
	stdscr.addstr(maxy-1,0, "C", curses.color_pair(1))
	stdscr.addstr(maxy-2,maxx-2, "D", curses.color_pair(1))
	stdscr.refresh()

	username = get_param("enter the username")

	while 1:
		stdscr.getch()

if __name__ == '__main__':
	print "hi"

	curses.wrapper(cursesMain)


