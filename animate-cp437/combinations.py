#!/usr/bin/env python3

import sys
import animate
import itertools

frames = []

red = (255,0,0)
green = (0,255,0)
blue = (0,0,255)

combinations = itertools.combinations(range(7), 3)
combinationsR = itertools.combinations_with_replacement(range(5), 3)

for c in combinations:
	lineC0 = [' ']*7
	lineC1 = ['o']*7
	for idx in c:
		lineC0[idx] = 'v'
		lineC1[idx] = 'x'

	line0 = ''.join(lineC0)
	line1 = ''.join(lineC1)

	frames.append('%s\n%s' % (line0, line1))

if not (sys.argv[1:] and sys.argv[1]=='write'):
	for f in frames:
		print(f)
		print('\n')

	sys.exit(0)

tmp = []
for f in frames:
	f = f.replace('v', '\x19')
	f = f.replace('x', '\x07')
	f = f.replace('o', '\x09')
	tmp.append(f)
frames = tmp

animate.setDelay(50);
animate.write(frames, 'combinations.gif')

