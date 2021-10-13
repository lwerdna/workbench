#!/usr/bin/env python

# test loop detection by comparison against miasm

import sys
from binaryninja import BinaryViewType
from helpers import *
from loops import get_loops

from miasm.core.graph import DiGraph

# given a dominator tree of graph, test if a->b
def test_dominate(dominator_tree, a, b):
    assert b in dominator_tree
    while True:
        if a==b: return True
        if b=='b0': break # did we reach top of tree?
        b = dominator_tree[b] # move up the dominator tree
    return False

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func = None if not sys.argv[2:] else sys.argv[2]

    (bv, func) = quick_get_func(fpath, None)
    if not bv:
        raise Exception('binary ninja didnt return analysis on -%s-' % fpath)

    functions = [func] if func else bv.functions
    for func in functions:
        print('-------- analyzing function %s --------' % func.name)

        # get binja's answer
        #
        answer_binja = set()
        for (i,loop) in enumerate(get_loops(func)):
            answer_binja.update([bbid(bb) for bb in loop])
        print('binja says:', answer_binja)

        # get miasm's answer
        #
        answer_miasm = set()
        G = miasm_graph_from_binja(func)
        for (header_footer, loop_body) in G.compute_natural_loops('b0'):
            print('header=%s footer=%s body=%s' % (header_footer[0], header_footer[1], loop_body))
            answer_miasm.update(loop_body)
        print('miasm says:', answer_miasm)

        # compare answers
        #
        if answer_binja == answer_miasm:
            print('PASS!')
        else:
            print('binja says:', answer_binja)
            print('miasm has, but binja does doesnt:', (answer_miasm - answer_binja))
            print('binja has, but miasm does doesnt:', (answer_binja - answer_miasm))

            reds = [bb for bb in func.basic_blocks if bbid(bb) in (answer_binja - answer_miasm)]
            blues = [bb for bb in func.basic_blocks if bbid(bb) in (answer_miasm - answer_binja)]
            graph_func('error_%s' % func.name, func, reds, blues)

            raise Exception('FAIL!')
