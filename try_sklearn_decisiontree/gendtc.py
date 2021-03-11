#!/usr/bin/env python
#
# read a python module containing 'input_names', 'input_ata', 'output_names', 'output_data'
# output a pickled list [<classifier>, x_names, y_names]
#
# the pickled list can then be used to graph, etc.

from sys import argv
import importlib
import helpers

if argv[1:]:
	fpath_data_module = argv[1]
	fpath_out = argv[2] if argv[2:] else '/tmp/tmp.pickle'
	
	data_module = importlib.import_module(fpath_data_module)
	clf = helpers.get_decision_tree_classifier(data_module.input_data, data_module.output_data)
	helpers.save_dtc(clf, data_module.input_names, data_module.output_names, fpath_out)
else:
	print('')
	print('Generate Decision Tree Classifier')
	print('')
	print('usage:')
	print('\t%s <input_data> <output_model>' % argv[0])
	print('')
	print('where:')
	print('\tinput_data is python module containing input_data, output_data, input_names, output_names')
	print('')
	print('examples:')
	print('\t%s sh4_data' % argv[0])
	print('\t%s z80_data' % argv[0])
	print('')

