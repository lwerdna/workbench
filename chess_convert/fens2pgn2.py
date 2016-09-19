#!/usr/bin/env python

# this version assumes a book number, subdirectories are
# the chapter number, and files are P.txt where P is the
# problem number

import os
import re
import sys

def getFen(fpath):
	fp = open(fpath)
	fen = fp.read().rstrip().lstrip()
	fp.close
	return fen

path = '.'
book = 2
if len(sys.argv)>1:
	path = sys.argv[1]
	m = re.match(r'^.*(\d)', path)
	if m:
		book = int(m.group(1))
print "using book number: %d" % book
print "searching for PGN's in: %s" % path

problems=[]
for (dirpath, dirnames, filenames) in os.walk(path):
	# accept only terminal dirs (with files, without dirs)
	if dirnames: continue

	m = re.match(r'.*/(\d+)$', dirpath)
	if not m:
		print "expected chapter subdir %s to end in digit" % dirpath
		assert(m)
	chap = int(m.group(1))

	for filename in filenames:
		fpath = os.path.join(dirpath, filename)
		m = re.match(r'^(\d+).txt$', filename)
		if not m:
			print "file %s is bad form" % fpath
			assert(m)
		prob = int(m.group(1))
		fen = getFen(fpath)
		problems.append([book,chap,prob,fen])
		print "book: %d" % book
		print "chap: %d" % chap
		print "prob: %d" % prob
		print " fen: %s" % fen
		print "----"

# sort with book having highest precedence, then chap#, then problem#
problems = sorted(problems, key=lambda x: x[0]*10000+x[1]*100+x[2])

# write pgn
fp = open('output.pgn', 'w')
for problem in problems:
	(book,chap,prob,fen) = problem
	left = 'Yusupov Book %d' % book
	right = 'Chapter %d Problem %d' % (chap,prob)
	# in case pgn browser lists by event type, put all info there
	fp.write('[Event "%s %s"]\n' % (left,right))
	fp.write('[Site "?"]\n')
	fp.write('[Date "????.??.??"]\n')
	fp.write('[Round "?"]\n')
	# in case pgn browser lists by player names, put info here
	fp.write('[White "%s"]\n' % left)
	fp.write('[Black "%s"]\n' % right)
	fp.write('[Result "*"]\n')
	fp.write('[FEN "%s"]\n\n *\n\n' % fen)
fp.close()

	
