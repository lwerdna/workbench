#!/usr/bin/env python

import sys
import time

table_data = []

def gui_thread():
	global table_data
	
	print('gui thread here')

	# pysimplegui window
	import PySimpleGUI as sg
	sg.theme('DarkGrey2')
	layout = [[sg.Table(values=table_data,
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

	print('creating window')
	window = sg.Window('Cyclomatic Complexity', layout, font='AndaleMono 16')

	print('event loop window')
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

	print('event loop done, closing')
	window.close()

def show_cyclomatic_complexity_table(bv):
	global table_data

	lookup = {}
	for f in bv.functions:
		blocks = list(f)
		n_edges = sum([len(b.outgoing_edges) for b in blocks])
		complexity = n_edges - len(blocks) + 2
		lookup[f.symbol.full_name] = { 'blocks': len(blocks), 'edges': n_edges, 'complexity': complexity }

	# load into table rows
	table_data = []
	for fname in sorted(lookup, key=lambda x: lookup[x]['complexity'], reverse=True):
		row = [fname, lookup[fname]['edges'], lookup[fname]['blocks'], lookup[fname]['complexity']]
		table_data.append(row)

	print(table_data)
	# launch gui
	import threading
	threading.Thread(target=gui_thread).start()
	#gui_thread()

#
from binaryninja.plugin import PluginCommand
PluginCommand.register("Cyclomatic Complexity", "Popup a GUI table with sorted cyclomatic complexities.", show_cyclomatic_complexity_table)
