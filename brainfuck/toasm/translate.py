#!/usr/bin/env python

import os, sys, re, pprint

print('; brainfuck assembly translation of %s\n' % sys.argv[1])

with open('prologue.s') as fp:
    print(fp.read())

with open(sys.argv[1]) as fp:
    code = fp.read()

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
for (i,c) in enumerate(code):
    if c == '>':
        print('\tinc rdi')
    elif c == '<':
        print('\tdec rdi')
    elif c == '+':
        print('\tinc byte [rdi]')
    elif c == '-':
        print('\tdec byte [rdi]')
    elif c == '.':
        print('\tcall output ; "%s"' % c)
    elif c == ',':
        print('\tcall input')
    elif c == '[':
        print('\tcmp byte[rdi], 0')
        print('\tjz loc_%d' % jmp[i]) 
        print('loc_%d:' % i)
    elif c == ']':
        print('\tcmp byte[rdi], 0')
        print('\tjnz loc_%d' % jmp[i])     
        print('loc_%d:' % i)
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

with open('epilogue.s') as fp:
    print(fp.read())
