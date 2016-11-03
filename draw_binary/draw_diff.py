#!/usr/bin/python

import os
import sys
import Levenshtein
from PIL import Image

IDX_BLACK = '\x00'
IDX_RED = '\x01'
IDX_WHITE = '\x02'
IDX_GREEN = '\x03'
color_lookup = [0xFFFFFF]*256
color_lookup[ord(IDX_BLACK)] = 0
color_lookup[ord(IDX_RED)] = 0xFF0000
color_lookup[ord(IDX_WHITE)] = 0xFFFFFF
color_lookup[ord(IDX_GREEN)] = 0x00FF00

###############################################################################
# main
###############################################################################
if __name__ == '__main__':
	if not sys.argv[3:]:
	    print "supply args! (width, binBefore, binAfter)"
	    sys.exit(-1);
	
	(width, aPath, bPath) = sys.argv[1:4]
	width = int(width)
	
	palette = []
	for rgb in color_lookup:
	    palette.append(rgb>>16)
	    palette.append((rgb>>8)&0xFF)
	    palette.append(rgb&0xFF)
	print palette

	f = open(aPath, 'rb')
	aBytes = f.read()
	f.close()
	f = open(bPath, 'rb')
	bBytes = f.read()
	size = f.tell()
	f.close()

	ops = Levenshtein.editops(aBytes, bBytes)
	print "done"

	data = ''
	last = 0
	for (op, aIdx, bIdx) in ops:
		# fill gap
		print "filling [%d,%d)" % (last,bIdx)
		data += (IDX_WHITE * (bIdx - last))

		if op == 'insert':
			print "delete at (%d,%d)" % (aIdx, bIdx)
			data += IDX_GREEN
		elif op == 'replace':
			print "insert at (%d,%d)" % (aIdx, bIdx)
			data += IDX_RED
		else:
			print "wtf is %s?" % op

		last = bIdx+1

	# given width and filesize, calculate height, and round up
	height = (size + (width-1))	/ width
	print "%d sized file to (%d,%d)" % (size, width, height)
	data += IDX_WHITE * (width*height - len(data))

	# "P" mode means 8-bit pixels that are indices into the palette	
	img = Image.frombuffer("P", (width, height), data, 'raw', "P", 0, 1)
	img.putpalette(palette)
	
	pathOut = os.path.basename(aPath) + '.png'
	print "saving %s\n" % pathOut
	img.save(pathOut)
