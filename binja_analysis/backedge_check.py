#!/usr/bin/env python

# test loop detection by comparison against NetworkX (graph theory library)

import sys
import networkx as nx
from helpers import *
from loops import get_loops

depths = {}
def assign_depth(bb, depth=0):
    global depths

    for child in [bbid(edge.target) for edge in bb.outgoing_edges]:
        if not child in depths:
            print('assigning %s depth %d' % (child, depth))
            depths[child] = 1

    depths[bb] = depth
    for edge in bb.outgoing_edges:
        assign_depth(edge.target, depth+1)

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func = None if not sys.argv[2:] else sys.argv[2]

    (bv, func) = quick_get_func(fpath, None)
    if not bv:
        raise Exception('binary ninja didnt return analysis on -%s-' % fpath)

    functions = [func] if func else bv.functions
    for func in functions:
        print('-------- analyzing function %s --------' % func.name)

        bblocks = list(func.basic_blocks)
        assign_depth(bblocks[0])

        G = nx_graph_from_binja(func)

        for bb in func.basic_blocks:
            for edge in bb.outgoing_edges:
                (header, footer) = (edge.target, edge.source)

                nx_back_edge = header.start <= footer.start
                #nx_back_edge = \
                #    nx.has_path(G, bbid(header), bbid(footer)) and \
                #    nx.shortest_path_length(G,'b0',bbid(header)) < nx.shortest_path_length(G,'b0',bbid(footer)) 

                if nx_back_edge != edge.back_edge:
                    raise Exception('is edge %s -> %s a non-strict back edge? networkx:%s binja:%s' %
                        (bbid(edge.source), bbid(edge.target), nx_back_edge, edge.back_edge))

