#!/usr/bin/env python

import os, sys

import sympy

import helpers

# return the conjuncts of a sympy expression
def get_conjuncts(expr):
    if type(expr) == sympy.And:
        return get_conjuncts(expr.args[0]) + get_conjuncts(expr.args[1])
    elif type(expr) == sympy.Symbol:
        return [expr]
    else:
        return []

class SeqNode(object):
    def __init__(self, *children):
        self.children = children

    # returns:
    #   True if refinedment made
    #   False otherwise
    def refine():
        return
#        for (i, c) in self.children:
#            if type(c) == CrudeNode:
#                break
#
#            if rc := c.refine():
#                
#        if i >= len(self.children):
#            return False
#
#        # are there crude nodes?
#        if any([c for c in self.children of type(c) == CrudeNode]):
#        
#
#        for (i, c) in self.children:
#            if type(c) == CrudeNode:
#                # find term in this 
#
#        for c in self.children:
#            if type(c) == 

    def __dot__(self):
        return f'SEQ'

class IfNode(object):
    def __init__(self, *children):
        self.children = children

    def refine():
        return any([c.refine() for c in self.children])

    def __dot__(self):
        return f'IF'

class RefinedNode(object):
    def __init__(self, block_id, cond):
        self.children = []
        self.block_id = block_id

    def refine():
        return False

    def __dot__(self):
        return f'REFINED\\lblock:{self.block_id}\\l'

class CrudeNode(object):
    def __init__(self, block_id, cond):
        self.children = []
        self.block_id = block_id
        self.cond = cond # reaching condition

    def refine():
        raise Exception('this shouldnt get called directly')

    def __dot__(self):
        return f'CRUDE\\lblock:{self.block_id}\\lcond:{self.cond}\\l'

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
    assert get_conjuncts(expr) == [A]

    B = sympy.Symbol('B')
    expr = A & B
    assert get_conjuncts(expr) == [A, B]

    expr = A | B
    assert get_conjuncts(expr) == []

    C = sympy.Symbol('C')
    expr = A & (B | C)
    assert get_conjuncts(expr) == [A]

    D, E, F = sympy.symbols('D E F')
    expr = (A&B | C&D | E)&F
    assert get_conjuncts(expr) == [F]

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

    print('PASS')
