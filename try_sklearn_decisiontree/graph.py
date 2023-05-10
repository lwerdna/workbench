#!/usr/bin/env python

import re
import sys
import helpers
from sklearn import tree
from subprocess import call

def postprocess_dot(fpath='/tmp/tmp.dot'):
	with open(fpath) as fp:
		linesIn = fp.readlines()

	linesOut = []
	for l in linesIn:
		l = re.sub(r'value = .*?\]', '', l)
		l = re.sub(r'gini = [\d\.]+\\n', '', l)
		l = re.sub(r'samples = \d+\\n', '', l)
		l = re.sub(r' <= 0.5', '=0', l)
		l = re.sub(r'\\nclass = ', '', l)
		l = re.sub(r' <= (\d+)\.\d+', r' <= \1', l)
		linesOut.append(l)

	with open(fpath, 'w') as fp:
		fp.write(''.join(linesOut))

def graph_classifier(clf, fpath_out, input_names=None, output_names=None):
	dot_data = tree.export_graphviz(clf, out_file='/tmp/tmp.dot',
			feature_names = input_names,
			class_names = output_names,
			filled = True,
			rounded = True			
	)

	postprocess_dot()

	call(['dot', '-Tsvg', '/tmp/tmp.dot', '-o', fpath_out])

if __name__ == '__main__':
	infile = sys.argv[1] if sys.argv[1:] else '/tmp/tmp.pickle'
	print('opening classifier from: %s' % infile)
	[classifier, input_names, output_names] = helpers.load_dtc(infile)

	outfile = sys.argv[2] if sys.argv[2:] else '/tmp/tmp.svg'
	print('saving graph to: %s' % outfile)
	graph_classifier(classifier, outfile, input_names, output_names)

