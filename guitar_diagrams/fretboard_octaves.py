#!/usr/bin/env python

import sys

n_frets = 20

# dark2 from matplotlib
palette = ['#1B9E77','#D95F02','#7570B3','#E7298A','#66A61E','#E6AB02','#A6761D','#666666']

notes = []
for octave in range(1,10):
	tmp = ['%s%d'%(x,octave) for x in ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']]
	notes.extend(tmp)

print('<h3>octaves mapped to color</h3>')
print('<table cellpadding=4>')

print('  <tr>')
for fret in range(n_frets):
	print('    <th>%d</th>' % fret)
print('  </tr>')

nocolor = sys.argv[1:] and sys.argv[1]=='nocolor'

for note in ['E4','B3','G3','D3','A2','E2']:
	print('  <tr>')
	for fret in range(n_frets):
		bgcolor = palette[int(note[-1])]
		if nocolor:
			bgcolor = '#e0e0e0'

		color = 'black'
		if nocolor:
			color = '#B0B0B0'
		print('    <td bgcolor="%s"><font color=%s>%s</font></td>' % (bgcolor, color, note))
		note = notes[notes.index(note)+1]
	print('  </tr>')

# https://en.wikipedia.org/wiki/Standard_tuning

print('</table>')
