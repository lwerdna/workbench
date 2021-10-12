#!/usr/bin/env python

# test loop detection by comparison against NetworkX (graph theory library)

import sys
from binaryninja import BinaryViewType
import networkx as nx
import helpers
from loops import get_loops

# return a string identifier for a given basic block node
def bbid(bb):
    return 'b%d' % bb.index

# convert a Binary Ninja CFG to a NetworkX directed graph
def binja_func_to_networkx_graph(func):
    G = nx.DiGraph()

    for src in func.basic_blocks:
        G.add_node(bbid(src))

        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_node(bbid(dst))
            G.add_edge(bbid(src), bbid(dst))
        
    return G

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func = None if not sys.argv[2:] else sys.argv[2]

    (bv, func) = helpers.quick_get_func(fpath, None)
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
        G = binja_func_to_networkx_graph(func)
        answer_nx = set()
        for cycle in nx.simple_cycles(G):
            print('nx cycle at:', cycle)
            answer_nx.update(cycle)
        print('networkx says:', answer_nx)

        # compare answers
        #
        if answer_binja == answer_nx:
            print('PASS!')
        else:
            raise Exception('FAIL!')
