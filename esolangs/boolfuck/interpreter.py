#!/usr/bin/env python

# boolfuck interpreter
# https://esolangs.org/wiki/Boolfuck

# like brainfuck, but:
# cells are 0/1 true/false GF(2) instead of uint8_t
# - command removed
# . command is input (was input)
# ; command is output (was ,)
# output is bits, little end of each byte first

import os, sys, re, pprint
from collections import defaultdict

debug = sys.argv[2:] and sys.argv[2] in ['debug', '-debug', '-dbg']
with open(sys.argv[1]) as fp:
    code = fp.read()

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
outbits = []
data = defaultdict(bool)
instr_ptr = 0
data_ptr = 0
while True: 
    if debug:
        print("memory:")
        for k in sorted(data):
            ptr = ' <--' if k==data_ptr else ''
            print('%02d: %d%s' % (k, data[k], ptr))
        print('code:')
        a = 'code[%d] = %s' % (instr_ptr, ''.join(code[max(instr_ptr-8, 0):instr_ptr]))
        b = '%c%s' % (code[instr_ptr], ''.join(code[instr_ptr+1:instr_ptr+1+8]))
        print(a+b)
        print(' '*len(a) + '^')
        input()

    c = code[instr_ptr]

    if c == '>':
        data_ptr += 1
    elif c == '<':
        data_ptr -= 1
    elif c == '+':
        data[data_ptr] = not data[data_ptr]
    elif c == ';':
        outbits.append(int(data[data_ptr]))
        if len(outbits) == 8:
            print(chr(int(''.join([str(b) for b in reversed(outbits)]), 2)), end='')
            outbits = []
    elif c == '.':
        data[data_ptr] = int(input())
    elif c == '[':
        if data[data_ptr] == 0:
            instr_ptr = jmp[instr_ptr]
    elif c == ']':
        if data[data_ptr] != 0:
            instr_ptr = jmp[instr_ptr]
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

    instr_ptr += 1
    if instr_ptr >= len(code):
        break


