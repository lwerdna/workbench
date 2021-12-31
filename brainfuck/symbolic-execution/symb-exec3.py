#!/usr/bin/env python

# replace sympy with z3

import os, sys, re, copy
from collections import defaultdict

# pip install z3-solver
import z3

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

debug = 1

class State(object):
    def __init__(self, ip):
        self.ip = ip
        self.expressions = {} # can't use DefaultDict since z3 vars need a name
        self.constraints = z3.BoolVal(True)
        self.children = []

        self.output_idx = 0
        self.input_idx = 0

    def expression_set(self, name, value):
        assert name == 'dp' or re.match(r'^cell\d+$', name) or name.startswith('output'), 'error: '+name

        expr = z3.simplify(value)

        if name.startswith('output') and debug > 0:
            extra = ' (char: \'%c\')' % expr.as_long() if self.expression_evaluable(name) else ''
            print(GREEN + 'set output expression %s = %s%s' % (name, expr, extra) + NORMAL)

        self.expressions[name] = expr

    def expression_get(self, name):
        if not name in self.expressions:
            if name.startswith('input'):
                self.expressions[name] = z3.BitVec(name, 8)
                if debug > 0:
                    print(GREEN + 'created symbolic variable: %s'%name + NORMAL)
            else:
                self.expressions[name] = z3.BitVecVal(0, 8)

        return self.expressions[name]

    def expression_evaluable(self, name):
        expr = self.expression_get(name)
        return z3.is_int_value(expr) or z3.is_bv_value(expr)

    def expression_evaluate(self, name):
        assert self.expression_evaluable(name)
        return self.expression_get(name).as_long()

    def constrain(self, expr):
        self.constraints = z3.simplify(z3.And(self.constraints, expr))

    def consistent(self):
        s = z3.Solver()
        s.add(self.constraints)
        return s.check() == z3.sat

    def current_cell(self):
        return 'cell%02d' % state.expression_evaluate('dp')

    def gen_input_sym_name(self):
        result = 'input%d' % self.input_idx
        self.input_idx += 1
        return result

    def gen_output_sym_name(self):
        result = 'output%d' % self.output_idx
        self.output_idx += 1
        return result

    def clone(self, children_too=False):
        s = copy.deepcopy(self)
        if not children_too:
            s.children = []
        return s

    def all_nodes(self):
        result = [self]
        for c in self.children:
            result.extend(c.all_nodes())
        return result

    def all_edges(self):
        result = []
        for c in self.children:
            result.append((self, c))
        for c in self.children:
            result.extend(c.all_edges())
        return result

    def str_recursive_lines(self, depth=0):
        lines = []
        indent = '  '*depth

        lines.append('%sip = %d' % (indent, self.ip))

        for name in sorted(self.expressions):
            expr = self.expressions[name]
            extra = ''

            if name.startswith('output'):
                if self.expression_evaluable(name):
                    extra = ' \'%c\'' % expr.as_long()
            lines.append('%s%s = %s%s' % (indent, name, str(expr), extra))

        #for c in self.constraints:
        #    lines.append('%s%s' % (indent, str(c)))
        lines.append('%s%s' % (indent, str(self.constraints)))

        if depth >= 0:
            for c in self.children:
                lines.extend(c.str_recursive_lines(depth+1))

        return lines

    def str_recursive(self, depth=0):
        return '\n'.join(self.str_recursive_lines(depth))

    def __str__(self):
        return self.str_recursive(-1)

def convert_dot(root):
    result = []
    result.append('digraph g {')

    result.append('\t// define vertices')
    for s in root.all_nodes():
        label = s.str_recursive(-1).replace('\n', '\\l')
        result.append('\t%d [shape="Mrecord" fontname="Courier New" label="%s"];' % (id(s), label))

    result.append('')

    result.append('\t// define edges')
    for (a,b) in root.all_edges():
        result.append('\t%d -> %d' % (id(a), id(b)))

    result.append('}')
    return '\n'.join(result)

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

    #root.expressions['input0'] = BitVec('input0', 8)
    #root.expressions['input1'] = BitVec('input1', 8)
    #root.expressions['input2'] = BitVec('input2', 8)
    root.expressions['dp'] = z3.IntVal(0)
    leaves = [root]

    # execute
    while(leaves):
        #print('writing dot')
        #with open('/tmp/tmp.dot', 'w') as fp:
        #    fp.write(convert_dot(root))

        state = leaves.pop(0)

        while True:
            if debug > 1:
                print('code[%d]: %c' % (state.ip, code[state.ip]))
                print(state)
                input()

            if state.ip >= len(code):
                break

            c = code[state.ip]

            if c == '>':
                state.expression_set('dp', state.expression_get('dp')+1)
            elif c == '<':
                state.expression_set('dp', state.expression_get('dp')-1)
            elif c == '+':
                cname = state.current_cell()
                state.expression_set(cname, state.expression_get(cname)+1)
            elif c == '-':
                cname = state.current_cell()
                state.expression_set(cname, state.expression_get(cname)-1)
            elif c == '.':
                rhs = state.current_cell()
                lhs = state.gen_output_sym_name()
                state.expression_set(lhs, state.expression_get(rhs))
            elif c == ',':
                lhs = state.current_cell()
                rhs = z3.BitVec(state.gen_input_sym_name(), 8)
                state.expression_set(lhs, rhs)
            elif c == ']':
                state.ip = bracket_match[state.ip]-1
            elif c == '[':
                name = state.current_cell()
                cond = state.expressions[name]

                if z3.is_bv_value(cond):
                    value = cond.as_long()
                    if value == 0:
                        state.ip = bracket_match[state.ip]
                else:
                    # into body
                    child = state.clone()
                    child.constrain(cond != 0)
                    child.ip = state.ip + 1
                    if child.consistent():
                        state.children.append(child)
                        leaves.append(child)
                    # over body
                    child = state.clone()
                    child.constrain(cond == 0)
                    child.ip = bracket_match[state.ip] + 1
                    if child.consistent():
                        state.children.append(child)
                        leaves.append(child)

                    break
            elif c == '*':
                debug = 100
            else:
                # ...possibly interspersed with other characters (which are ignored)
                pass

            state.ip += 1
            if state.ip >= len(code):
                break

        #print('--------------------------------------')
        #print(root.str_recursive())

    #print(root.str_recursive())
    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write(convert_dot(root))
