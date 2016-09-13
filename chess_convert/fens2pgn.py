#!/usr/bin/env python

import os
import re

def getFen(filename):
	fp = open('./fens/'+filename)
	fen = fp.read().rstrip().lstrip()
	fp.close
	return fen

problems=[]
for (dirpath, dirnames, filenames) in os.walk('./fens'):
	for filename in filenames:
		m = re.match(r'^(\d+)_(\d+)_(\d+).txt$', filename)
		assert(m)
		fen = getFen(filename)
		(book,chap,prob) = map(int, m.group(1,2,3))
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

	
