#!/usr/bin/env python

# Use sympy when executing BF to track expressions per data cells, inputs, outputs.
# It does NOT support branching.

import os, sys, re, pprint
from collections import defaultdict

import sympy

debug = 0
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

def ename_to_int(name):
    expr = expressions[name]
    assert expr.is_integer, 'cannot evaluate "%s" to int' % name
    return int(expr.evalf())

expressions = defaultdict(lambda: sympy.core.numbers.Integer(0))

# manually created symbols
#expressions['d0'] = sympy.symbols('d0')

output_idx = 0
input_idx = 0
instr_ptr = 0
while True:
    if 1:
        print('%04d: %c' % (instr_ptr, code[instr_ptr]))
        print('expressions:')
        for (k, v) in expressions.items():
            print('%s: %s' % (k, v))
        input()

    c = code[instr_ptr]

    if c == '>':
        expressions['dp'] += 1
    elif c == '<':
        expressions['dp'] -= 1
    elif c == '+':
        name = 'd%d' % ename_to_int('dp')
        expressions[name] = (expressions[name] + 1) % 256
    elif c == '-':
        name = 'd%d' % ename_to_int('dp')
        expressions[name] = (expressions[name] - 1) % 256
    elif c == '.':
        name = 'd%d' % ename_to_int('dp')
        deepcopy = sympy.sympify(str(expressions[name]))
        expressions['output%d' % output_idx] = deepcopy
        output_idx += 1
    elif c == ',':
        name = 'd%d' % ename_to_int('dp')
        expressions[name] = sympy.symbols('input%d' % input_idx)
        input_idx += 1
        # data[data_ptr] = int(input())
    elif c == '[':
        name = 'd%d' % ename_to_int('dp')
        if ename_to_int(name) == 0:
            instr_ptr = jmp[instr_ptr]
    elif c == ']':
        name = 'd%d' % ename_to_int('dp')
        if ename_to_int(name) != 0:
            instr_ptr = jmp[instr_ptr]
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

    instr_ptr += 1
    if instr_ptr >= len(code):
        break

for (k, v) in expressions.items():
    extra = ''
    if k.startswith('output'):
        extra = " '%c'" % v
    print('%s: %s%s' % (k, v, extra))


