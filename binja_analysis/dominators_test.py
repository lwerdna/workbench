#!/usr/bin/env python

# test loop detection by comparison against NetworkX (graph theory library)

import sys
import networkx as nx
from helpers import *
from loops import get_loops

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func = None if not sys.argv[2:] else sys.argv[2]

    (bv, func) = quick_get_func(fpath, None)
    if not bv:
        raise Exception('binary ninja didnt return analysis on -%s-' % fpath)

    functions = [func] if func else bv.functions
    for func in functions:
        print('-------- analyzing function %s --------' % func.name)

        G = nx_graph_from_binja(func)

        for bb in func.basic_blocks:
            print('for basic block %s' % bbid(bb))

            # get binja's answer
            #
            answer_binja = set([bbid(x) for x in bb.dominators])
            print('binja says:', answer_binja)

            # get networkx's answer
            #
            answer_nx = set(nx_dominators(G, bbid(bb)))
            print('networkx says:', answer_nx)

            # compare answers
            #
            if answer_binja == answer_nx:
                print('PASS!')
            else:
                raise Exception('FAIL!')
