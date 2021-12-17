#!/usr/bin/env python

# branching support

import os, sys, re, copy
from collections import defaultdict

import sympy

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

debug = 1

class State(object):
    def __init__(self, ip):
        self.ip = ip
        self.expressions = defaultdict(lambda: sympy.core.numbers.Integer(0))
        self.constraints = []
        self.children = []
        self.trace = []

        self.output_idx = 0
        self.input_idx = 0

    def trace_mark(self):
        self.trace.append(self.ip)

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

    def constraint_violation(self, name, value):
        for c in self.constraints:
            if c.subs(name, value) == False:
                return True
        return False

    def clone(self, children_too=False):
        s = copy.deepcopy(self)
        if not children_too:
            s.children = []
        return s

    def birth(self):
        baby = self.clone()
        self.children.append(baby)
        return baby

    def str_recursive_lines(self, depth=0):
        lines = []
        indent = '  '*depth

        lines.append(indent + '----------------')
        lines.append(indent + 'trace: ' + '-'.join(map(str, self.trace)))
        for (k, v) in self.expressions.items():
            extra = ''
            if k.startswith('output') and v.is_integer:
                extra = " '%c'" % v
            lines.append('%s%s: %s%s' % (indent, k, v, extra))

        for c in self.constraints:
            lines.append('%s%s' % (indent, str(c)))

        if depth >= 0:
            for c in self.children:
                lines.extend(c.str_recursive_lines(depth+1))

        return lines

    def str_recursive(self, depth=0):
        return '\n'.join(self.str_recursive_lines(depth))

    def __str__(self):
        return self.str_recursive(-1)

if __name__ == '__main__':
    with open(sys.argv[1]) as fp:
        code = fp.read()
        code = re.sub(r'[^\+\-,\.\[\]><]', '', code)

    code = list(code)
    code = [c for c in code if not c.isspace()]

    # validate matching []'s
    bracket_match = {}
    stack = []
    for (i,c) in enumerate(code):
        if c == '[':
            stack.append(i)
        elif c == ']':
            bracket_match[stack[-1]] = i
            bracket_match[i] = stack.pop()

    # setup
    root = State(0)
    root.trace_mark()

    #root.expressions['input0'] = sympy.Integer(2)
    #root.expressions['input1'] = sympy.Integer(4)
    #root.expressions['input2'] = sympy.Integer(6)
    leaves = [root]

    # execute
    while(leaves):
        state = leaves.pop(0)

        while True:
            if debug > 1:
                print('%d: %c' % (state.ip, code[state.ip]))
                print(state)
                input()

            autoincrement_ip = True

            if state.ip >= len(code):
                break

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
                    print(GREEN+'generated output expression named: %s'%lhs+NORMAL)
                if lhs == 'output5':
                    breakpoint()
                state.expressions[lhs] = state.expressions[rhs]
            elif c == ',':
                lhs = 'd%d' % state.expression_as_int('dp')
                rhs = state.gen_input_sym_name()

                if rhs in state.expressions:
                    expr = state.expressions[rhs]
                    if debug > 0:
                        print(GREEN+'using existing input value: %s'%expr+NORMAL)
                    state.expressions[lhs] = expr
                else:
                    if debug > 0:
                        print(GREEN+'generated input symbol: %s'%rhs+NORMAL)
                    state.expressions[lhs] = sympy.Symbol(rhs)
                # data[data_ptr] = int(input())
            elif c in ('[', ']'):
                name = 'd%d' % state.expression_as_int('dp')
                if state.expressions[name].is_integer:
                    value = state.expression_as_int(name)
                    if (c == '[' and value == 0) or \
                       (c == ']' and value != 0):
                        autoincrement_ip = False
                        state.ip = bracket_match[state.ip]+1
                else:
                    eq_zero = sympy.core.relational.Eq(state.expressions[name], 0)
                    ne_zero = sympy.core.relational.Ne(state.expressions[name], 0)

                    if not eq_zero in state.constraints:
                        baby = state.birth()
                        baby.constraints.append(ne_zero)
                        baby.ip = bracket_match[state.ip]+1 if c=='[' else state.ip+1
                        baby.trace_mark()
                        leaves.append(baby)

                    if not ne_zero in state.constraints:
                        baby = state.birth()
                        baby.constraints.append(eq_zero)
                        baby.ip = bracket_match[state.ip]+1 if c==']' else state.ip+1
                        baby.trace_mark()
                        leaves.append(baby)

                    # stop executing the current state
                    break
            else:
                # ...possibly interspersed with other characters (which are ignored)
                pass

            if autoincrement_ip:
                state.ip += 1

            if state.ip >= len(code):
                break

        #print('--------------------------------------')
        #print(root.str_recursive())
        
    print('--------------------------------------')
    print(root.str_recursive())
