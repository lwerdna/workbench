#!/usr/bin/env python

import os, sys, re, readline
from collections import defaultdict

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

instruction_chars = ['+', '-', '>', '<', '.', ',', '[', ']', '*']

(strip, debug_foreground) = (False, False)
for option in sys.argv[2:]:
    strip = strip or option in ['strip', '-strip', '--strip']
    debug_foreground = debug_foreground or option in ['debug', '-debug', '-dbg']

print('strip:', strip)
print('debug:', debug_foreground)

with open(sys.argv[1]) as fp:
    code = fp.read()
    if strip:
        code = re.sub(r'[^\+\-,\.\[\]><\*]', '', code)
code = re.sub(r'\s', ' ', code)

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
while instr_ptr < len(code):
    if debug_foreground or instr_ptr in breakpoints:
        if instr_ptr in breakpoints:
            breakpoints.remove(instr_ptr)
        debug_foreground = 1
        while 1:
            print("memory @%d:" % data_ptr)
            for k in sorted(data):
                ptr = ' <--' if k==data_ptr else ''
                print('%02d: %d%s' % (k, data[k], ptr))
            print('code @%d:' % instr_ptr)
            before = code[max(instr_ptr-16, 0): min(len(code)-1, instr_ptr)]
            after = code[min(instr_ptr+1, len(code)-1): min(len(code)-1, instr_ptr+16)]
            print(f'{before}{code[instr_ptr]}{after}')
            print(' '*len(before) + '^')
            print('breakpoints: ' + ', '.join(map(str, breakpoints)))
            cmd = input('DEBUG> ')
            if cmd in ['c', 'continue', 'g', 'go']:
                debug_foreground = False
                break
            elif cmd in ['pydbg', 'pydebug']:
                breakpoint()
            elif cmd.startswith('bp '):
                breakpoints.add(int(cmd[3:]))
            elif cmd.startswith('bc '):
                breakpoints.remove(int(cmd[3:]))
            elif cmd == 'l':
                i = 0
                while True:
                    chunk = code[i:i+10]
                    print('%04d: %s' % (i, ' '.join(list(chunk))))
                    if len(chunk) < 10:
                        break
                    i += 10
            elif cmd == 'q':
                sys.exit(-1)
            else:
                break

    c = code[instr_ptr]

    auto_increment = True
    if c == '>':
        data_ptr += 1
        data[data_ptr]
    elif c == '<':
        data_ptr -= 1
        data[data_ptr]
    elif c == '+':
        data[data_ptr] = (data[data_ptr] + 1) % 256
    elif c == '-':
        data[data_ptr] = (data[data_ptr] - 1) % 256
    elif c == '.':
        print(GREEN+chr(data[data_ptr])+NORMAL, end='')
    elif c == ',':
        d = input()
        data[data_ptr] = int(d) if d else 10
    elif c == '[':
        if data[data_ptr] == 0:
            instr_ptr = jmp[instr_ptr]
    elif c == ']':
        instr_ptr = jmp[instr_ptr]
        auto_increment = False
    elif c == '*':
        debug_foreground = True
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

    if auto_increment:
        instr_ptr += 1

    while instr_ptr < len(code) and not code[instr_ptr] in instruction_chars:
        instr_ptr += 1
