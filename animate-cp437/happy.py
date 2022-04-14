#!/usr/bin/env python3

import animate

frames = []

frames.append('''

[000000]
''')
frames.append('''
 \x19
[\x0100000]
''')
frames.append('''
  \x19
[0\x010000]
''')
frames.append('''
   \x19
[00\x01000]
''')
frames.append('''
    \x19
[000\x0100]
''')
frames.append('''
     \x19
[0000\x010]
''')
frames.append('''
      \x19
[00000\x01]
''')

# filters
for i in range(len(frames)): # remove start blank line, end blank line
	tmp = frames[i].split('\n')
	if not tmp[0]:
		tmp = tmp[1:]
	if not tmp[-1]:
		tmp = tmp[0:-1]
	frames[i] = '\n'.join(tmp)
	
animate.write(frames, 'happy.gif')
