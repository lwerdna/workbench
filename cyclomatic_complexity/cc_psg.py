#!/usr/bin/env python

import sys
import time

import PySimpleGUI as sg

import binaryninja
from binaryninja.binaryview import BinaryViewType

if __name__ == '__main__':
	fpath = sys.argv[1]

	# analyze
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

	# load into table rows
	data = []
	for fname in sorted(lookup, key=lambda x: lookup[x]['complexity'], reverse=True):
		row = [fname, lookup[fname]['edges'], lookup[fname]['blocks'], lookup[fname]['complexity']]
		data.append(row)

	# pysimplegui window
	sg.theme('DarkGrey2')
	layout = [[sg.Table(values=data,
						headings=['   function   ', ' edges ', ' blocks ', '  cc  '],
						max_col_width=25,
						auto_size_columns=True,
						display_row_numbers=False,
						justification='left',
						num_rows=20,
						key='-TABLE-',
						row_height=20,
						change_submits=True,
						bind_return_key=True
						)],
			 ]

	window = sg.Window('Cyclomatic Complexity', layout, font='AndaleMono 16')

	# ------ Event Loop ------
	(last_row_clicked, last_time_clicked) = (0, 0)
	while True:
		event, values = window.read()
		print(event, values)
		if event == sg.WIN_CLOSED:
			break
		elif event == '-TABLE-':
			row = values['-TABLE-'][0]
			now = time.time()
			if row==last_row_clicked and (now-last_time_clicked)<.25:
				print('you double clicked row %d' % row)
			(last_row_clicked, last_time_clicked) = (row, now)

	window.close()

