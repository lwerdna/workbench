#!/usr/bin/env python

# detect loops

import os, sys, re

from helpers import *

(bv, func) = quick_get_func()
print_function_disasm(func)
graph_func(func.name, func, [], [])

# find back edges 
# B -> A when A dominates B
# A is the top or "header" of loop
# B is the bottom of loop
back_edges = []
for bb in func.basic_blocks:
    for edge in bb.outgoing_edges:
        if edge.back_edge:
            back_edges.append(edge)
            print('back edge %s -> %s' % (bbid(edge.source), bbid(edge.target)))

# collect all nodes between header and bottom
reds_all = []

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
    reds = list(loop_blocks)
    graph_func('loop_%s_%s' % (bbid(header), bbid(footer)), func, reds, [])

    reds_all.extend(reds)

graph_func('loops', func, reds_all, [])
