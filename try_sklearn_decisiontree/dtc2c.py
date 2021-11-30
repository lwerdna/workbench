#!/usr/bin/env python

# https://scikit-learn.org/stable/auto_examples/tree/plot_unveil_tree_structure.html#sphx-glr-auto-examples-tree-plot-unveil-tree-structure-py

import re
import sys
import helpers
from sklearn import tree

# list where each entry is 
def get_value_name(node):
	vlist = values[node][0]
	assert len(vlist) == len(output_names)
	assert len(list(filter(lambda x:x, vlist))) == 1
	idx = [i for i,x in enumerate(vlist) if x][0]
	return re.sub(r'[^\w\d]', '_', output_names[idx])

def recur(node:int, depth=0):
	indent = ' '*depth

	# leaf node
	if children_left[node] == children_right[node] == -1:
		print(indent+'return %s();' % get_value_name(node))
		return

	if threshold[node] >= 0:
		operator = '<='
	else:
		print('WTF! node %d has threshold %d' % (node, threshold[node]))

	#print(indent + 'if(%s %s %d) {' % \
	print(indent + 'if(%s %s %d)' % \
		(input_names[feature[node]], operator, threshold[node]))
		
	recur(children_left[node], depth+1)
	#print(indent + '}')
	#print(indent + 'else {')
	print(indent + 'else')
	recur(children_right[node], depth+1)
	#print(indent + '}')

if __name__ == '__main__':
	infile = sys.argv[1] if sys.argv[1:] else '/tmp/tmp.pickle'
	print('// opening classifier from: %s' % infile)
	[classifier, input_names, output_names] = helpers.load_dtc(infile)

	print('// n_nodes: %d' % classifier.tree_.node_count)
	print('// n_leaves: %d' % classifier.tree_.n_leaves)
	print('// max_depth: %d' % classifier.tree_.max_depth)

	n_nodes = classifier.tree_.node_count
	children_left = classifier.tree_.children_left
	children_right = classifier.tree_.children_right
	feature = classifier.tree_.feature
	threshold = classifier.tree_.threshold
	values = classifier.tree_.value

	recur(0)
