#!/usr/bin/env python

# - states become objects with idea of children, so they can form a tree

import os, sys, re, pprint
from collections import defaultdict

import sympy

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

debug = 0

class State(object):
    def __init__(self, ip):
        self.ip = ip
        self.expressions = defaultdict(lambda: sympy.core.numbers.Integer(0))
        self.children = []

        self.output_idx = 0
        self.input_idx = 0

    def gen_input_sym_name(self):
        result = 'input%d' % self.input_idx
        self.input_idx += 1
        return result

    def gen_output_sym_name(self):
        result = 'output%d' % self.output_idx
        self.output_idx += 1
        return result

    def expression_as_int(self, name):
        expr = self.expressions[name]
        assert expr.is_integer, 'cannot evaluate "%s" to int' % name
        return int(expr.evalf())

    def str_recursive(self, depth=0):
        lines = []

        for (k, v) in self.expressions.items():
            extra = ''
            if k.startswith('output') and v.is_integer:
                extra = " '%c'" % v
            lines.append('%s%s: %s%s' % ('  '*depth, k, v, extra))

        if depth >= 0:
            for c in self.children:
                lines.extend(c.str_recursive(depth+1))

        return '\n'.join(lines)

    def __str__(self):
        return self.str_recursive(-1)

if __name__ == '__main__':
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

    # setup
    root = State(0)
    leaves = [root]

    # execute
    while(leaves):
        state = leaves.pop(0)

        while True:
            if debug > 1:
                print('%d: %c' % (state.ip, code[state.ip]))
                print(state)
                input()

            c = code[state.ip]

            if c == '>':
                state.expressions['dp'] += 1
            elif c == '<':
                state.expressions['dp'] -= 1
            elif c == '+':
                name = 'd%d' % state.expression_as_int('dp')
                state.expressions[name] = (state.expressions[name] + 1) % 256
            elif c == '-':
                name = 'd%d' % state.expression_as_int('dp')
                state.expressions[name] = (state.expressions[name] - 1) % 256
            elif c == '.':
                rhs = 'd%d' % state.expression_as_int('dp')
                lhs = state.gen_output_sym_name()
                if debug > 0:
                    print(GREEN+'generated output symbol: %s'%lhs+NORMAL)
                state.expressions[lhs] = state.expressions[rhs]
            elif c == ',':
                lhs = 'd%d' % state.expression_as_int('dp')
                rhs = state.gen_input_sym_name()
                if debug > 0:
                    print(GREEN+'generated input symbol: %s'%rhs+NORMAL)
                state.expressions[lhs] = sympy.Symbol(rhs)
                # data[data_ptr] = int(input())
            elif c == '[':
                name = 'd%d' % state.expression_as_int('dp')
                if state.expression_as_int(name) == 0:
                    state.ip = jmp[state.ip]
            elif c == ']':
                name = 'd%d' % state.expression_as_int('dp')
                if state.expression_as_int(name) != 0:
                    state.ip = jmp[state.ip]
            else:
                # ...possibly interspersed with other characters (which are ignored)
                pass

            state.ip += 1
            if state.ip >= len(code):
                break

    print(root)
