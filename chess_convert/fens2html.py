#!/usr/bin/env python

import os
import re

def getFen(filename):
	fp = open('./fens/'+filename)
	fen = fp.read().rstrip().lstrip()
	fp.close
	return fen

def problemToFname(problem):
	(book,chap,prob,fen) = problem
	return 'problem_%02d_%02d_%02d.html' % (book,chap,prob)

problems=[]
for (dirpath, dirnames, filenames) in os.walk('./fens'):
	for filename in filenames:
		m = re.match(r'^(\d+)_(\d+)_(\d+).txt$', filename)
		assert(m)
		fen = getFen(filename)
		(book,chap,prob) = map(int, m.group(1,2,3))
		problems.append([book,chap,prob,fen])

# sort with book having highest precedence, then chap#, then problem#
problems = sorted(problems, key=lambda x: x[0]*10000+x[1]*100+x[2])

# write html
fname = 'board_%d_%d_%d' % (book,chap,prob)

for (i,problem) in enumerate(problems):
	(book,chap,prob,fen) = problem
	html_name = problemToFname(problem)
	fp = open(html_name, 'w')
	fp.write('<html>\n')
	fp.write('	<head>\n')
	fp.write('		<link rel="stylesheet" href="css/chessboard-0.3.0.min.css" />\n')
	fp.write('		<script src="http://code.jquery.com/jquery-1.10.1.min.js"></script>\n')
	fp.write('		<script src="js/chess.min.js"></script>\n')
	fp.write('		<script src="js/chessboard-0.3.0.min.js"></script>\n')
	fp.write('		<script src="js/puzzle.js"></script>\n')
	fp.write('	</head>\n')
	fp.write('	<body>\n')
	fp.write('		<div id="board" style="width: 400px"></div>\n')
	fp.write('		<script>\n')
	fp.write('			var fen = \'%s\';\n' % fen)
	fp.write('			var game = engineGame(fen);\n')
	fp.write('		</script>\n')
	fp.write('\n')
	fp.write('<p>Yusupov Book %d Chapter %d Problem %d</p>\n' % (book,chap,prob))
	if(fen.split(' ')[1]=='w'):
		fp.write('<p>White to play!</p>\n')
	else:
		fp.write('<p>Black to play!</p>\n')
	fp.write('<p>')
	if i != 0:
		fp.write('<a href="%s">&lt;previous</a>&nbsp;' % problemToFname(problems[i-1]))
	if i != len(problems)-1:
		fp.write('<a href="%s">next&gt;</a>' % problemToFname(problems[i+1]))
	fp.write('</p>\n');
	fp.write('</body>\n');
	fp.write('</html>\n');
	fp.close();
	
