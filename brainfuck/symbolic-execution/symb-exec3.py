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

        self.last_constraints = ''

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

    def consistent(self, code_len=None):
        if self.ip < 0:
            print(RED + 'state failed consistency test self.ip (%d) < 0' % self.ip + NORMAL)
            #breakpoint()
            return False

        if code_len != None and self.ip >= code_len:
            print(RED + 'state failed consistency test self.ip (%d) >= %d' % (self.ip, code_len) + NORMAL)
            #breakpoint()
            return False

        dp = self.expression_evaluate('dp')
        if dp < 0:
            print(RED + 'state failed consistency test dp (%d) < 0' % dp + NORMAL)
            #breakpoint()
            return False

        # avoid solving the same constraints repeatedly
        if str(self.constraints) != self.last_constraints:
            s = z3.Solver()
            s.add(self.constraints)
            if s.check() != z3.sat:
                return False
            self.last_constraints = str(self.constraints)

        return True

    def current_cell(self):
        return 'cell%02d' % self.expression_evaluate('dp')

    def gen_input_symbol(self):
        name = 'input%d' % self.input_idx
        self.input_idx += 1
        var = z3.BitVec(name, 8)
        if debug > 0:
            print(GREEN + 'created symbolic variable: %s' % var + NORMAL)
        return var

    def gen_output_sym_name(self):
        result = 'output%02d' % self.output_idx
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

# given a state and the code, decide whether to continue this path
def continue_path(state, code):
    if not state.consistent():
        return False

    #if code[state.ip:].startswith('[[-]>[-]<+++++++++[->+'):
    #    breakpoint()

#    if state.expression_evaluate('output11') != ord('C'):
#        print(RED + 'badboy path detected' + NORMAL)
#        return False
#
#    if state.ip == 1283:
#        print(RED + 'badboy path detected' + NORMAL)
#        return False
#
#    if \
#        state.expression_evaluate('output59') == ord('S'): # and \
#        #state.expression_evaluate('output60') == ord('o') and \
#        #state.expression_evaluate('output61') == ord('r') and \
#        #state.expression_evaluate('output62') == ord('r') and \
#        #state.expression_evaluate('output63') == ord('y'):
#        print(RED + 'badboy path detected' + NORMAL)
#        return False

    if state.input_idx > 8:
        print(RED + 'guessing the password is too long' + NORMAL)
        return False

    return True



def main():
    global debug

    with open(sys.argv[1]) as fp:
        code = fp.read()
        code = re.sub(r'[^\+\-,\.\[\]><\*]', '', code)

    code = ''.join([c for c in list(code) if not c.isspace()])

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

    #root.expressions['input0'] = z3.BitVecVal(65, 8)
    #root.expressions['input1'] = z3.BitVecVal(66, 8)
    #root.expressions['input2'] = z3.BitVecVal(10, 8)
    root.expressions['dp'] = z3.IntVal(0)
    leaves = [root]

    # execute
    while(leaves):
        print('writing dot')
        with open('/tmp/tmp.dot', 'w') as fp:
            fp.write(convert_dot(root))

        state = leaves.pop(0)

        while True:
            #if state.ip == 1189:
            #    breakpoint()
            if debug > 0:
                before = code[state.ip-8:state.ip]
                after = code[state.ip+1:state.ip+9]
                #print('ip:%d    ...%s %c %s...' % (state.ip, before, code[state.ip], after))
                #print('dp:%d' % (state.expression_evaluate('dp')))
                print('ip:%d dp:%d' % (state.ip, state.expression_evaluate('dp')))
            if debug > 1:
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
                rhs = state.gen_input_symbol()
                state.expression_set(lhs, rhs)
            elif c == ']':
                state.ip = bracket_match[state.ip]-1
            elif c == '[':
                name = state.current_cell()
                cond = state.expression_get(name)

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
            if not continue_path(state, code):
                break

        #print('--------------------------------------')
        #print(root.str_recursive())

    #print(root.str_recursive())
    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write(convert_dot(root))

if __name__ == '__main__':
    if 0:
        import cProfile
        cProfile.run('main()')
    else:
        main()
