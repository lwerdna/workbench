#!/usr/bin/env python
#
# calculate cyclomatic complexity of functions identified with Binary Ninja
#
# $ ./thisfile.py /path/to/mybinary.exe

import os
import sys

import binaryninja
from binaryninja.binaryview import BinaryViewType

if __name__ == '__main__':
	fpath = sys.argv[1]

	# load functions (from cache or bndb)
	print('analyzing')
	bv = BinaryViewType.get_view_of_file(fpath)
	bv.update_analysis_and_wait()

	lookup = {}
	for f in bv.functions:
		blocks = list(f)
		n_edges = sum([len(b.outgoing_edges) for b in blocks])
		# this seems too easy to calculate independent paths
		# M = E - N + P (https://en.wikipedia.org/wiki/Cyclomatic_complexity)
		complexity = n_edges - len(blocks) + 2
		lookup[f.symbol.full_name] = { 'blocks': len(blocks), 'edges': n_edges, 'complexity': complexity }

	for fname in sorted(lookup, key=lambda x: lookup[x]['complexity'], reverse=True):
		print('%s() edges=%d blocks=%d complexity=%d' %
			(fname, lookup[fname]['edges'], lookup[fname]['blocks'], lookup[fname]['complexity']))

	#
	print('done')

