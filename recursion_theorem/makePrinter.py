#!/usr/bin/env python

import sys

def makePrinter(x):
	return 'tape='+repr(x)

if __name__ == '__main__':
	fp = open(sys.argv[1], 'r')
	stuff = fp.read()
	fp.close()
	print makePrinter(stuff)
