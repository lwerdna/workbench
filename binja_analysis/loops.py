#!/usr/bin/env python

# detect loops

import os, sys, re

from helpers import *

# return list for each loops
# each loop is a list of basic blocks
# eg:
# [[b0,b1,b2], [b7,b8,b9]] means two loops, the first with {b0,b1,b2}, the second with {b7,b8,b9}
def get_loops(func):
    loops = []

    # find back edges (B -> A when A dominates B)
    # A is called "header", B is called "footer"
    back_edges = []
    for bb in func.basic_blocks:
        for edge in bb.outgoing_edges:
            if edge.back_edge:
                back_edges.append(edge)
                print('back edge %s -> %s' % (bbid(edge.source), bbid(edge.target)))

    # collect all nodes between header and footer
    for edge in back_edges:
        (header, footer) = (edge.target, edge.source)
        print('collecting blocks for loop fenced between %s and %s:' % (bbid(header), bbid(footer)))
        loop_blocks = set([header, footer])
        if header != footer:
            queue = [edge.source]
            while queue:
                cur = queue.pop(0)
                loop_blocks.add(cur)
                new_batch = [e.source for e in cur.incoming_edges if (not e.source in loop_blocks)]
                queue.extend(new_batch)
        print(','.join([bbid(n) for n in loop_blocks]))

        # store this loop
        loops.append(list(loop_blocks))

    return loops

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    fname = '_some_loops' if not sys.argv[2:] else sys.argv[2]
    (bv, func) = quick_get_func(fpath, fname)
    print_function_disasm(func)

    graph_func(func.name, func, [], [])

    all_loop_blocks = []

    for (i,loop) in enumerate(get_loops(func)):
        graph_func('loop_%d' % i, func, loop, [])
        all_loop_blocks.extend(loop)

    graph_func('loop_all', func, all_loop_blocks, [])
