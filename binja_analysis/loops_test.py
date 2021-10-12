#!/usr/bin/env python

# test loop detection by comparison against NetworkX (graph theory library)

import sys
from binaryninja import BinaryViewType
import networkx as nx
from helpers import *
from loops import get_loops

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

        # get networkx's answer
        #
        # We could just compare to the same algorithm implemented in networkx here, but then there is risk
        # of getting it wrong twice, of verifying wrong vs. wrong.
        # Instead, inefficiently detect all cycles then filter when head dominates tail so that it comes at
        # the problem from a different angle.
        G = nx_graph_from_binja(func)
        dominator_tree = nx.immediate_dominators(G, 'b0') # cache dominator tree for fast lookup
        answer_nx = set()
        for cycle in nx.simple_cycles(G):
            print('nx cycle at:', cycle)
            if len(cycle) == 1:
                answer_nx.update(cycle)
            else:
                # [A,B,C] is returned for cycles:
                # {A->B->C->A, B->C->A->B, C->A->B->C}
                n = len(cycle)
                for rotation in range(n):
                    (head, tail) = (cycle[0+rotation], cycle[(n-1+rotation)%n])
                    #print('testing if head %s is in dominators %s = %s' % (head, tail, nx_dominators(G, tail)))
                    if test_dominate(dominator_tree, head, tail):
                        #print('PASS!')
                        answer_nx.update(cycle)
        print('networkx says:', answer_nx)

        # compare answers
        #
        if answer_binja == answer_nx:
            print('PASS!')
        else:
            print('binja says:', answer_binja)
            print('networkx has, but binja does doesnt:', (answer_nx - answer_binja))
            print('binja has, but networkx does doesnt:', (answer_binja - answer_nx))

            reds = [bb for bb in func.basic_blocks if bbid(bb) in (answer_binja - answer_nx)]
            blues = [bb for bb in func.basic_blocks if bbid(bb) in (answer_nx - answer_binja)]
            graph_func('error_%s' % func.name, func, reds, blues)

            raise Exception('FAIL!')
