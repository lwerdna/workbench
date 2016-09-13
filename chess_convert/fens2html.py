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

# sort with book having highest precedence, then chap#, then problem#
problems = sorted(problems, key=lambda x: x[0]*10000+x[1]*100+x[2])

# write html
fp = open('output.html', 'w')
fp.write('<html>\n')
fp.write('<head>\n')
fp.write('  <meta charset="utf-8" />\n')
fp.write('  <meta http-equiv="X-UA-Compatible" content="IE=edge,chrome=1" />\n')
fp.write('  <title>Multiple Boards Example</title>\n')
fp.write('  <base href="http://chessboardjs.com/" />\n')
fp.write('\n')
fp.write('  <link rel="stylesheet" href="css/chessboard.css" />\n')
fp.write('</head>\n')
fp.write('<body>\n')
for problem in problems:
	(book,chap,prob,fen) = problem
	id_ = 'board_%d_%d_%d' % (book,chap,prob)
	fp.write('<h3>Chapter %d Problem %d</h3>\n' % (chap,prob))
	fp.write('<div id="%s" style="width: 400px"></div>\n' % id_)
fp.write('<script src="js/json3.min.js"></script>\n')
fp.write('<script src="js/jquery-1.10.1.min.js"></script>\n')
fp.write('<script src="js/chessboard.js"></script>\n')
fp.write('<script>\n')
fp.write('var init = function() {\n')
for problem in problems:
	(book,chap,prob,fen) = problem
	id_ = 'board_%d_%d_%d' % (book,chap,prob)
	fp.write('var %s = ChessBoard(\'%s\', \'%s\');\n' % (id_, id_, fen))
fp.write('}; // end init()\n')
fp.write('$(document).ready(init);\n')
fp.write('</script>\n')
fp.write('</body>\n')
fp.write('</html>\n')
fp.close()

	
