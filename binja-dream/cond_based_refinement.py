#!/usr/bin/env python

import os, sys

import sympy

import helpers

# return the conjuncts of a sympy expression
def get_conjuncts(expr):
    if type(expr) == sympy.And:
        return get_conjuncts(expr.args[0]).union(get_conjuncts(expr.args[1]))
    elif type(expr) == sympy.Symbol:
        return {expr}
    else:
        return {}

# is C or ~C a conjunct of expr?
def involved(expr, c):
    conjuncts = get_conjuncts(expr)
    return c in conjuncts or ~c in conjuncts

class SeqNode(object):
    def __init__(self, *children):
        self.children = list(children)

    # returns:
    #   True if refinement made
    #   False otherwise
    def refine(self):
        for i,child in enumerate(self.children):
            if isinstance(child, CrudeNode):
                if child.cond == True:
                    self.children[i] = RefinedNode(child.block_id)
                    return True
                break

            if child.refine():
                return True

        # if we refined nothing, return so
        if i == len(self.children):
            return False

        # search for most common conjunct from here, rightward
        breakpoint()
        for conj in get_conjuncts(self.children[i].cond):
            j = i
            while j < len(self.children) and involved(self.children[j].cond, conj):
                j += 1
            print(f'{conj} is involved in children [{i}, {j}]')

        return False

    def __dot__(self):
        return f'SEQ'

class IfNode(object):
    def __init__(self, *children):
        self.children = list(children)

    def refine(self):
        return any([c.refine() for c in self.children])

    def __dot__(self):
        return f'IF'

class RefinedNode(object):
    def __init__(self, block_id):
        self.children = []
        self.block_id = block_id

    def refine(self):
        return False

    def __dot__(self):
        return f'REFINED\\lblock:{self.block_id}\\l'

class CrudeNode(object):
    def __init__(self, block_id, cond):
        self.children = []
        self.block_id = block_id
        self.cond = cond # reaching condition

    def refine(self):
        raise Exception('this shouldnt get called directly')

    def __dot__(self):
        return f'CRUDE\\lblock: {self.block_id}\\lcond: {self.cond}\\l'

def cbr2dot(root):
    dot = []
    dot.append('digraph G {')

    # global graph settings
    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')

    # node list
    def all_nodes(n):
        return [n] + sum([all_nodes(c) for c in n.children], [])

    dot.append('// nodes')
    for n in all_nodes(root):
        dot.append(f'{id(n)} [label="{n.__dot__()}"];')

    def all_edges(n):
        result = [(n, c) for c in n.children]
        result = result + sum([all_edges(c) for c in n.children], [])
        return result

    # edge list
    dot.append('// edges')
    for (a, b) in all_edges(root):
        dot.append(f'{id(a)} -> {id(b)}')

    dot.append('}')

    return '\n'.join(dot)

def draw_cbr(root, fbase='/tmp/tmp'):
    finput = fbase+'.dot'
    foutput = fbase+'.png'

    dot = cbr2dot(root)
    with open(finput, 'w') as fp:
        fp.write(dot)

    cmd = f'dot {finput} -Tpng -o {foutput}'
    print(cmd)
    os.system(cmd)

if __name__ == '__main__':
    # simple tests
    A = sympy.Symbol('A')
    expr = A
    assert get_conjuncts(expr) == {A}
    assert involved(expr, A)
    assert involved(expr, ~A)

    B = sympy.Symbol('B')
    expr = A & B
    assert get_conjuncts(expr) == {A, B}
    assert involved(expr, A)
    assert involved(expr, ~A)
    assert involved(expr, B)
    assert involved(expr, ~B)

    expr = A | B
    assert get_conjuncts(expr) == {}
    assert not involved(expr, A)
    assert not involved(expr, ~A)
    assert not involved(expr, B)
    assert not involved(expr, ~B)

    C = sympy.Symbol('C')
    expr = A & (B | C)
    assert get_conjuncts(expr) == {A}

    D, E, F = sympy.symbols('D E F')
    expr = (A&B | C&D | E)&F
    assert get_conjuncts(expr) == {F}
    assert involved(expr, F)
    assert involved(expr, ~F)
    assert not involved(expr, A)
    assert not involved(expr, ~A)
    assert not involved(expr, B)
    assert not involved(expr, ~B)    

    # create a test SEQ to be refined
    C2, C5 = sympy.symbols('C2 C5')
    root = SeqNode(
        CrudeNode(2, True),
        CrudeNode(5, C2),
        CrudeNode(6, ~C2),
        CrudeNode(9, C2 & C5),
        CrudeNode(10, ~C2 & ~C5),
        CrudeNode(13, True)
    )

    draw_cbr(root, 'test')

    step = 0
    while True:
        if not root.refine():
            break

        draw_cbr(root, f'refine{step}')
        step += 1

    print('PASS')
