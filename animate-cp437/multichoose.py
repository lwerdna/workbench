#!/usr/bin/env python3

import sys
import animate
import itertools

frames = []

red = (255,0,0)
green = (0,255,0)
blue = (0,0,255)

combinations = list(itertools.combinations(range(7), 3))
combinationsR = list(itertools.combinations_with_replacement(range(5), 3))

for i in range(len(combinations)):
	c = combinations[i]
	lineH0 = '     C(7,3)'
	lineH1 = '-----------'
	lineC0 = [' ']*7
	lineC1 = list('ABCDEFG')
	word = ''
	for idx in c:
		lineC0[idx] = '^'
		word += lineC1[idx]

	lineC0 = ''.join(lineC0)
	lineC1 = ''.join(lineC1) + ' ' + word

	c = combinationsR[i]
	zlineH0 = 'multiC(5,3)'
	zlineH1 = '-----------'
	zlineArr0 = list('     ')
	zlineArr0[c[0]] = '^'
	zlineArr1 = list('     ')
	zlineArr1[c[1]] = '^'
	zlineArr2 = list('     ')
	zlineArr2[c[2]] = '^'
	zlineC1 = list('12345')
	zword = ''
	for idx in c:
		zword += zlineC1[idx]

	zlineC1 = ''.join(zlineC1) + '   ' + zword;
	zlineArr0 = ''.join(zlineArr0)
	zlineArr1 = ''.join(zlineArr1)
	zlineArr2 = ''.join(zlineArr2)

	lines = []
	lines.append(lineH0 + '   ' + zlineH0)
	lines.append(zlineH1 + '   ' + zlineH1)
	lines.append(lineC1 + '   ' + zlineC1)
	lines.append(lineC0 + '       ' + zlineArr0)
	lines.append('              ' + zlineArr1)
	lines.append('              ' + zlineArr2)

	frames.append('\n'.join(lines))

if not (sys.argv[1:] and sys.argv[1]=='write'):
	for f in frames:
		print(f)
		print('\n')

	sys.exit(0)

tmp = []
for f in frames:
	f = f.replace('^', '\x18')
	f = f.replace('v', '\x19')
	f = f.replace('x', '\x07')
	f = f.replace('o', '\x09')
	tmp.append(f)
frames = tmp

animate.setDelay(50);
animate.write(frames, 'multichoose.gif')

