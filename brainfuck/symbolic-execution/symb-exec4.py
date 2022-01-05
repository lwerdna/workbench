#!/usr/bin/env python

# add interactive console/debugger

import os, sys, re, copy, readline, signal
from collections import defaultdict

# pip install z3-solver
import z3

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

debug_settings = \
{
    'foreground': True,
    'auto_graph': True,
    'breakpoints': set(),
    'countdown': 0,
    'last_command': '',
    'show_state': True,
    'quit': False
}

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

        if name.startswith('output'):
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

    def get_id(self, ident):
        if str(id(self)).endswith(str(ident)):
            return self
        if id(self) % 100000 == ident:
            return self
        for c in self.children:
            result = c.get_id(ident)
            if result:
                return result

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

        lines.append('state id: %d' % id(self))
        lines.append('%sip = %d' % (indent, self.ip))

        for name in sorted(self.expressions):
            expr = self.expressions[name]
            extra = ''

            if name.startswith('output'):
                if self.expression_evaluable(name):
                    value = expr.as_long()
                    extra = ' \'%c\'' % value if value >= 32 and value <= 126 else ''
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

def graph(root, current, fpath='/tmp/tmp.dot'):
    result = []
    result.append('digraph g {')

    result.append('\t// define vertices')
    for s in root.all_nodes():
        extra = ' color="red"' if current and id(current) == id(s) else ''
        label = s.str_recursive(-1).replace('\n', '\\l').replace('"', '&quote;')
        result.append('\t%d [shape="Mrecord" fontname="Courier New" label="%s"%s];' % (id(s), label, extra))

    result.append('')

    result.append('\t// define edges')
    for (a,b) in root.all_edges():
        result.append('\t%d -> %d' % (id(a), id(b)))

    result.append('}')

    print(GREEN + 'writing %s' % fpath + NORMAL)
    with open(fpath, 'w') as fp:
        fp.write('\n'.join(result))

    fpath2 = os.path.splitext(fpath)[0] + '.png'
    print(GREEN + 'writing %s' % fpath2 + NORMAL)
    os.system('dot %s -Tpng -o %s' % (fpath, fpath2))

# given a state and the code, decide whether to continue this path
def continue_path(state, code):
    if state.ip < 0 or state.ip >= len(code):
        return False

    if not state.consistent():
        return False

    if state.input_idx > 8:
        print(RED + 'guessing the password is too long' + NORMAL)
        return False

    return True

def signal_handler(sig, foo):
    global debug_settings
    debug_settings['foreground'] = True

def main():
    global debug_settings

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
    queue = [root]

    signal.signal(signal.SIGINT, signal_handler)

    # execute
    while True:
        state = None
        if queue:
            state = queue.pop()

        while True:
            # next activation should show debugger state
            debug_settings['show_state'] = True

            # debugger activates when queue is empty
            if not state:
                print(f'{GREEN}debug event: empty queue{NORMAL}')
                debug_settings['foreground'] = True

            # debugger activates when a countdown finishes
            if debug_settings['countdown']:
                debug_settings['countdown'] -= 1

                if debug_settings['countdown'] == 0:
                    debug_settings['foreground'] = True
                    print(f'{GREEN}debug event: countdown finished{NORMAL}')

            # debugger maybe activates when [
            if state and code[state.ip] == '[' and debug_settings['stop_on_open_bracket']:
                debug_settings['foreground'] = True
                print(f'{GREEN}debug event: \'[\' encountered{NORMAL}')

            # debugger activates when execution engine is about to split states
            if state and code[state.ip] == '[':
                if not z3.is_bv_value(state.expression_get(state.current_cell())):
                    if debug_settings['stop_on_branch']:
                        debug_settings['foreground'] = True
                        print(f'{GREEN}debug event: imminent state split{NORMAL}')

            # debugger activates when a breakpoint is hit
            if state and state.ip in debug_settings['breakpoints']:
                debug_settings['foreground'] = True
                print(f'{GREEN}debug event: breakpoint hit at {state.ip}{NORMAL}')

            # activate debugger?
            if debug_settings['foreground']:
                # activating debugger cancels previous conditions
                debug_settings['countdown'] = 0
                debug_settings['stop_on_open_bracket'] = False
                debug_settings['stop_on_branch'] = False

                while 1:
                    if debug_settings['show_state']:
                        if state:
                            before = code[max(0, state.ip-8):state.ip]
                            after = code[state.ip+1:min(len(code)-1, state.ip+9)]
                            print(f'ip:{state.ip}    ...{before}{RED}[{NORMAL}{code[state.ip]}{RED}]{NORMAL}{after}...')
                            print(f'dp:{state.expression_evaluate("dp")}')
                            print(f'{len(queue)} states in queue')
                        else:
                            print(f'{RED}no state{NORMAL}')

                        if debug_settings['auto_graph']:
                            graph(root, state)

                        debug_settings['show_state'] = False

                    cmd = input('CMD> ')
                    if cmd == '':
                        cmd = debug_settings['last_command']
                    debug_settings['last_command'] = cmd

                    # step
                    if cmd in ['s', 'n']:
                        break
                    # go <number_of_steps>
                    elif re.match(r'^g \d+$', cmd):
                        debug_settings['countdown'] = int(cmd[2:])
                        debug_settings['foreground'] = False
                        print(f'{GREEN}going for {debug_settings["countdown"]} steps{NORMAL}')
                        break
                    # go until open bracket
                    elif cmd in ['[']:
                        debug_settings['foreground'] = False
                        debug_settings['stop_on_open_bracket'] = True
                        break
                    # go until branch or split
                    elif cmd in ['gb', 'gs']:
                        debug_settings['foreground'] = False
                        debug_settings['stop_on_branch'] = True
                        break
                    # go unconditionally
                    elif cmd in ['g', 'go', 'c', 'continue']:
                        debug_settings['foreground'] = False
                        break
                    # breakpoints
                    elif re.match(r'^bp \d+$', cmd):
                        debug_settings['breakpoints'].add(int(cmd[3:]))
                    elif re.match(r'^bc \d+$', cmd):
                        debug_settings['breakpoints'].remove(int(cmd[3:]))
                    elif cmd == 'bl':
                        print('breakpoints:')
                        for addr in sorted(debug_settings['breakpoints']):
                            print(addr)
                    # set state
                    elif cmd.startswith('set '):
                        ident = int(cmd[4:])
                        tmp = root.get_id(ident)
                        if tmp:
                            queue = []
                            state = tmp
                            debug_settings['show_state'] = True
                            print(f'{GREEN}set state to id {id(state)}{NORMAL}')
                        else:
                            print(f'{RED}couldn\'t find state with id {ident}{NORMAL}')
                    # graph
                    elif cmd == 'graph':
                        graph(root, state)
                    elif cmd in ['graph_auto', 'auto_graph']:
                        debug_settings['auto_graph'] = not debug_settings['auto_graph']
                        print(f'{GREEN}set auto_graph to: {debug_settings["auto_graph"]}{NORMAL}')
                    # quit
                    elif cmd == 'q':
                        debug_settings['quit'] = True
                        break
                    else:
                        print(f'unrecognized command: {cmd}')

                if debug_settings['quit']:
                    state = None
                    queue = []
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
                    # over body
                    child = state.clone()
                    child.constrain(cond == 0)
                    child.ip = bracket_match[state.ip] + 1
                    if child.consistent():
                        state.children.append(child)
                        queue.append(child)
                    # into body
                    child = state.clone()
                    child.constrain(cond != 0)
                    child.ip = state.ip + 1
                    if child.consistent():
                        state.children.append(child)
                        queue = [child] + queue

                    break
            else:
                # ...possibly interspersed with other characters (which are ignored)
                pass

            state.ip += 1
            if not continue_path(state, code):
                break

        #print('--------------------------------------')
        #print(root.str_recursive())

if __name__ == '__main__':
    if 0:
        import cProfile
        cProfile.run('main()')
    else:
        main()
