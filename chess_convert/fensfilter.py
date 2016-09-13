#!/usr/bin/env python

import os
import re
import subprocess

t = r'[rnbqkpRNBQKP12345678]{1,8}'
regexFenPosition = r'^('+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+'/'+t+')$'
regexFen = regexFenPosition[:-1] + r' [wb] (?:(?:K?Q?k?q?)|-) (?:(?:[a-h][1-8])|-) \d+ \d+$'

def getFen(filename):
	fp = open('./fens/'+filename)
	fen = fp.read().rstrip().lstrip()
	fp.close
	return fen

def fix(filename):
	subprocess.call(['fastfen', './fens/'+filename])

problems=[]
for (dirpath, dirnames, filenames) in os.walk('./fens'):
	for filename in filenames:
		m = re.match(r'^(\d+)_(\d+)_(\d+).txt$', filename)
		assert(m)
		fen = getFen(filename)

		m = re.match(regexFen, fen)
		if not m:
			print "%s with fen %s is not valid" % (filename, fen)
			fix(filename)

		position = m.group(1)
		if re.search(r'q.*q', position):
			print "%s with fen %s has two black queens!" % (filename, fen)
			fix(filename)
		if re.search(r'Q.*Q', position):
			print "%s with fen %s has two white queens!" % (filename, fen)
			fix(filename)
		if re.search(r'k.*k', position):
			print "%s with fen %s has two black kings!" % (filename, fen)
			fix(filename)
		if re.search(r'K.*K', position):
			print "%s with fen %s has two white kings!" % (filename, fen)
			fix(filename)

		(rank8,x,x,x,x,x,x,rank1) = position.split('/')
		if re.search(r'[pP]', rank8):
			print "%s with fen %s has pawns on the 8th rank!" % (filename, fen)
			fix(filename)
		if re.search(r'[pP]', rank1):
			print "%s with fen %s has pawns on the 1st rank!" % (filename, fen)
			fix(filename)
		


	
