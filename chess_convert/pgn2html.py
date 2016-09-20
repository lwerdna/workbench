#!/usr/bin/env python

import os
import re
import sys

import chess
import chess.pgn

def eventToFname(event):
	return re.sub(r'\W', '_', event)+'.html'

if __name__ == '__main__':
	assert(len(sys.argv)==3)
	[pathPgn,pathOutput] = sys.argv[1:3]
	print "using PGN: %s" % pathPgn
	print "using output: %s" % pathPgn

	# read the file -> problems list
	problems = []
	pgn = open(pathPgn)
	while 1:
		game = chess.pgn.read_game(pgn)
		if not game: break
		event = game.headers['Event']
		fen = game.headers['FEN']
		assert(event and fen)
		problems.append({'event':event,'fen':fen})
	pgn.close()

	# for each of the problems -> generate html
	for (i,prob) in enumerate(problems):
		nameHtml = eventToFname(prob['event'])
		pathHtml = os.path.join(pathOutput, nameHtml)
		print "writing %s" % pathHtml
		fp = open(pathHtml, 'w')
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
		fp.write('			var fen = \'%s\';\n' % prob['fen'])
		fp.write('			var game = engineGame(fen);\n')
		fp.write('		</script>\n')
		fp.write('\n')
		fp.write('<p>%s</p>\n' % prob['event'])
		if(prob['fen'].split(' ')[1]=='w'):
			fp.write('<p>White to play!</p>\n')
		else:
			fp.write('<p>Black to play!</p>\n')
		fp.write('<p>')
		if i != 0:
			fp.write('<a href="%s">&lt;previous</a>&nbsp;' % eventToFname(problems[i-1]['event']))
		if i != len(problems)-1:
			fp.write('<a href="%s">next&gt;</a>' % eventToFname(problems[i+1]['event']))
		fp.write('</p>\n');
		fp.write('</body>\n');
		fp.write('</html>\n');
		fp.close();
		
