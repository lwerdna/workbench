#!/usr/bin/env python

import z3

from parser import parse, ExprNode, AndNode, OrNode, NotNode, ValNode, VarNode

from subprocess import Popen, PIPE

class TruthTable(object):
    def __init__(self, n_inputs, n_outputs):
        self.n_inputs = n_inputs
        self.n_outputs = n_outputs

        self.rows = []

    def add(self, inputs, outputs):
        assert len(inputs) == self.n_inputs
        assert len(outputs) == self.n_outputs
        irow = [str(int(i)) for i in inputs]
        orow = [str(int(o)) for o in outputs]
        self.rows.append(''.join(irow) + ' ' + ''.join(orow))

    def minimize(self):
        # form input
        lines = []
        lines.append(f'.i {self.n_inputs}')
        lines.append(f'.o {self.n_outputs}')
        lines.append(f'.type f')
        lines.extend(self.rows)
        lines.append('.e')
        script = '\n'.join(lines).encode('utf-8')
        #print('INPUT:')
        #print(script)

        # pipe to espresso
        process = Popen('espresso', stdin=PIPE, stdout=PIPE, stderr=PIPE)
        (stdout, stderr) = process.communicate(script)
        stdout = stdout.decode("utf-8")
        stderr = stderr.decode("utf-8")
        #print('stdout: -%s-' % stdout)
        #print('stderr: -%s-' % stderr)
        process.wait()

        # products is list of (literals, negated_literals)
        # where each is a set of integers identifying the literal variables involved in that product
        # eg:
        # ({0,1,4}, {2}) means v0 && v1 && !v2 && v4
        products = []

        for line in stdout.split('\n'):
            if not line or line.isspace():
                continue
            if line.startswith('.'):
                continue

            # line like "1- 1"
            #print('line: ' + line)
            (inputs, outputs) = line.split(' ')
            assert len(inputs) == self.n_inputs
            assert len(outputs) == self.n_outputs
            assert outputs == '1'*self.n_outputs

            lits = {i for (i,c) in enumerate(inputs) if c=='1'}
            nlits = {i for (i,c) in enumerate(inputs) if c=='0'}
            products.append((lits, nlits))

        return products

# convert a z3 expression to a python expression
# eg: Or(A, And(Not(A), B)) -> 'A or ((not A) and B)'
def python_bool_expr_z3(expr):
    if expr.children() == []:
        return str(expr)

    lines = [python_bool_expr_z3(c) for c in expr.children()]

    match str(expr.decl()):
        case 'Not':
            assert len(lines) == 1
            return f'(not {lines[0]})'
        case 'And':
            return '(' + ' and '.join(lines) + ')'
        case 'Or':
            return '(' + ' or '.join(lines) + ')'
        case _:
            breakpoint()

# return variables of a z3 expression
# eg: Or(A, And(Not(A), B)) -> [A, B]
def variables_z3(expr):
    if expr.children() == []:
        return {expr}

    result = set()
    for c in expr.children():
        result.update(variables_z3(c))

    return result

# eg:
# ['A','B','C'] -> {'A':False, 'B':False, 'C':False}, {'A':False, 'B':False, 'C':True}, ...
def bool_gen(varnames):
    n = len(varnames)
    for i in range(2**n):
        yield {name: bool(i & (1<<(n-pos-1))) for (pos, name) in enumerate(varnames)}

# minimize a z3 expression
def minimize_z3(expr):
    variables = variables_z3(expr)
    var_names = [str(c) for c in variables]
    expr_py = python_bool_expr_z3(expr)

    tt = TruthTable(len(var_names), 1)
    for inputs in bool_gen(var_names):
        #print(f'evaluating {expr_py} under {inputs}')
        result = eval(expr_py, {}, inputs)

        tt_inputs = [int(inputs[n]) for n in var_names]
        tt_outputs = [int(result)]
        #print(f'tt_inputs: {tt_inputs}')
        #print(f'tt_outputs: {tt_outputs}')
        tt.add(tt_inputs, tt_outputs)

    sum_ = True
    for product in tt.minimize():
        (lits, nlits) = product

        product = True
        for i in lits:
            product = z3.And(variables[i])

def minimize(expr):
    if type(expr) == str:
        expr = parse(expr)

    vnames = list(expr.varnames())

    tt = TruthTable(len(vnames), 1)
    for inputs in bool_gen(vnames):
        #print(f'evaluating {expr} under {inputs}')
        result = expr.evaluate(inputs)

        tt_inputs = inputs.values()
        tt_outputs = [int(result)]
        #print(f'tt_inputs: {tt_inputs}')
        #print(f'tt_outputs: {tt_outputs}')
        tt.add(tt_inputs, tt_outputs)

    sum_ = ValNode(False)

    for product in tt.minimize():
        (lits, nlits) = product

        product = ValNode(True)
        for i in lits:
            product = AndNode([VarNode(vnames[i]), product])
        for i in nlits:
            product = AndNode([NotNode(VarNode(vnames[i])), product])

        sum_ = OrNode([product, sum_])

    result = sum_.prune_vals()

    return result

def minimize_str(expr:str):
    etree = parse(expr)
    assert etree
    etree2 = minimize_etree(etree)
    return str(etree2)

if __name__ == '__main__':
    import sys

    # A + /AB
    # should simplify to
    # A + B
    tt = TruthTable(2, 1)
    tt.add([0, 0], [0])
    tt.add([0, 1], [1])
    tt.add([1, 0], [1])
    tt.add([1, 1], [1])
    #print(tt.minimize())

    # A + /AB + /A/B
    tt = TruthTable(2, 1)
    tt.add([0, 0], [1])
    tt.add([0, 1], [1])
    tt.add([1, 0], [1])
    tt.add([1, 1], [1])
    #print(tt.minimize())

    # A+/AB  ->  A+B
    tmp = minimize('A or (not A and B)')
    assert str(tmp) in ['(A or B)', '(B or A)']

    # A/B + AB  ->  A
    tmp = minimize('(A and not B) or (A and B)')
    assert str(tmp) == 'A'

    # /A/B/C + /A/BC  ->  /A/B
    tmp = minimize('(not A and not B and not C) or (not A and not B and C)')
    assert str(tmp) in ['((not B) and (not A))', '((not A) and (not B))']

    # /X/YZ + /XYZ + X/Y  - > /XZ + X/Y
    tmp = minimize('(not X and not Y and Z) or (not X and Y and Z) or (X and not Y)')
    assert str(tmp) in ['(((not X) and Z) or ((not Y) and X))',
                        '(((not Y) and X) or ((not X) and Z))']
