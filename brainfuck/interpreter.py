#!/usr/bin/env python

import os, sys, re, pprint
from collections import defaultdict

(strip, debug) = (False, False)
for option in sys.argv[2:]:
    strip = strip or option in ['strip', '-strip', '--strip']
    debug = debug or option in ['debug', '-debug', '-dbg']

print('strip:', strip)
print('debug:', debug)

with open(sys.argv[1]) as fp:
    code = fp.read()
    if strip:
        code = re.sub(r'[^\+\-,\.\[\]><\*]', '', code)

code = list(code)
code = [c for c in code if not c.isspace()]

# validate matching []'s
jmp = {}
stack = []
for (i,c) in enumerate(code):
    if c == '[':
        stack.append(i)
    elif c == ']':
        jmp[stack[-1]] = i
        jmp[i] = stack.pop()

#
data = defaultdict(int)
instr_ptr = 0
data_ptr = 0
breakpoints = set()
while True: 
    #if instr_ptr == 1189:
    #    debug = 1
    #print('ip:%d dp:%d' % (instr_ptr, data_ptr))
    if debug or instr_ptr in breakpoints:
        debug = 1
        while 1:
            print("memory (data_ptr: %d)" % data_ptr)
            for k in sorted(data):
                ptr = ' <--' if k==data_ptr else ''
                print('%02d: %d%s' % (k, data[k], ptr))
            print('code:')
            a = 'code[%d] = %s' % (instr_ptr, ''.join(code[max(instr_ptr-8, 0):instr_ptr]))
            b = '%c%s' % (code[instr_ptr], ''.join(code[instr_ptr+1:instr_ptr+1+8]))
            print(a+b)
            print(' '*len(a) + '^')
            print('breakpoints: ' + ', '.join(map(str, breakpoints)))
            cmd = input('DEBUG>')
            if cmd in ['c', 'continue', 'g', 'go']:
                debug = False
                break
            elif cmd.startswith('bp '):
                breakpoints.add(int(cmd[3:]))
            elif cmd.startswith('bc '):
                breakpoints.remove(int(cmd[3:]))
            else:
                break

    c = code[instr_ptr]

    if c == '>':
        data_ptr += 1
    elif c == '<':
        data_ptr -= 1
    elif c == '+':
        data[data_ptr] = (data[data_ptr] + 1) % 256
    elif c == '-':
        data[data_ptr] = (data[data_ptr] - 1) % 256
    elif c == '.':
        print(chr(data[data_ptr]), end='')
    elif c == ',':
        data[data_ptr] = int(input())
    elif c == '[':
        if data[data_ptr] == 0:
            instr_ptr = jmp[instr_ptr]
    elif c == ']':
        if data[data_ptr] != 0:
            instr_ptr = jmp[instr_ptr]
    elif c == '*':
        debug = True
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

    instr_ptr += 1
    if instr_ptr >= len(code):
        break



