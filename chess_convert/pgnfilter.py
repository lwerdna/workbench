#!/usr/bin/env python

import os
import re
import sys
import subprocess

# https://python-chess.readthedocs.io
import chess
import chess.pgn

t = r'[rnbqkpRNBQKP12345678]{1,8}'
regexFenPosition = r'^('+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+')$'
regexFen = regexFenPosition[:-1] + r' [wb] (?:(?:K?Q?k?q?)|-) (?:(?:[a-h][1-8])|-) \d+ \d+$'

def fix(filename):
	subprocess.call(['fastfen', './fens/'+filename])

if __name__ == '__main__':
	pathPgn = './output.pgn'
	if sys.argv[1:]:
		pathPgn = sys.argv[1]
	print "opening PGN: %s" % pathPgn
	pgn = open(pathPgn)

	lineCur = 1   
	lineToOffset = {}
	while 1:
		lineToOffset[lineCur] = pgn.tell()
		if not pgn.readline():
			break;
		lineCur += 1
	pgn.seek(0)

	print lineToOffset
	sys.exit(-1)

 
	gameNum = 1
	while 1:
		game = chess.pgn.read_game(pgn)
		fen = game.headers["FEN"]
		print "offset:%d, game:%d, fen:%s" % (pgn.tell(), gameNum, fen)
	
		m = re.match(regexFen, fen)
		if not m:
			print "%s is not valid" % fen
			fix(filename)
	
		position = m.group(1)
		if re.search(r'q.*q', position):
			print "%s has two black queens!" % fen
			fix(filename)
		if re.search(r'Q.*Q', position):
			print "%s has two white queens!" % fen
			fix(filename)
		if re.search(r'k.*k', position):
			print "%s has two black kings!" % fen
			fix(filename)
		if re.search(r'K.*K', position):
			print "%s has two white kings!" % fen
			fix(filename)
	
		if not re.search(r'K', position):
			print "%s is missing a white king!" % fen
			fix(filename)
		if not re.search(r'k', position):
			print "%s is missing a black king!" % fen
			fix(filename)
	
		(rank8,x,x,x,x,x,x,rank1) = position.split('/')
		if re.search(r'[pP]', rank8):
			print "%s has pawns on the 8th rank!" % fen
			fix(filename)
		if re.search(r'[pP]', rank1):
			print "%s has pawns on the 1st rank!" % fen
			fix(filename)
		
		gameNum += 1
	
