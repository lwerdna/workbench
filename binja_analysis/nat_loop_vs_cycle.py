#!/usr/bin/env python

# Q: is the natural loop detection algorithm the same as cycle detection with dominator check?
# A: no, here is a counterexample
#
#     a <-----+
#     |       |
#     v       |
#     b ----+ |
#     |     | |
#     v     | |
# +-- c <-+ | |
# |   |   | | |
# |   v   | | |
# |   d   | | |
# |   |   | | |
# |   v   | | |
# |   e --+ | |
# |   ^     | |
# |   |     | |
# |   +-----+ |
# |           |
# +-> f ------+

import os, sys, re, pprint
import networkx as x
from helpers import *

def natural_loops(DG):
    result = set()

    back_edges = []
    for (src, dst) in DG.edges():
        if dst in nx_dominators(DG, src, 'a'):
            back_edges.append((src, dst))
            print('back edge %s -> %s' % (src, dst))

    # reverse breadth-first search from footer to header, collecting all nodes
    for (footer, header) in back_edges:
        print('collecting blocks for loop fenced between %s and %s:' % (header, footer))
        subloop_nodes = set([header, footer])
        if header != footer:
            queue = [footer]
            while queue:
                cur = queue.pop(0)
                subloop_nodes.add(cur)
                new_batch = [edge[0] for edge in DG.in_edges(cur) if (not edge[0] in subloop_nodes)]
                print('incoming nodes to %s: %s' % (cur, new_batch))
                queue.extend(new_batch)

        print('subloop nodes:', subloop_nodes)

        # store this loop
        result.update(list(subloop_nodes))

    return result

def cycle_method(DG):
    result = set()

    for cycle in nx.simple_cycles(DG):
        print('cycle: ', cycle)

        if len(cycle) == 1:
            result.update(cycle)
        else:
            # [A,B,C] is returned for cycles:
            # {A->B->C->A, B->C->A->B, C->A->B->C}
            n = len(cycle)
            for rotation in range(n):
                (head, tail) = (cycle[0+rotation], cycle[(n-1+rotation)%n])
                print('testing if head %s is in dominators %s = %s' % (head, tail, nx_dominators(DG, tail, 'a')))
                if head in nx_dominators(DG, tail, 'a'):
                    print('PASS! adding loop', cycle)
                    result.update(cycle)
        
    return result

DG = nx.DiGraph()
DG.add_edge('a', 'b')
DG.add_edge('b', 'c')
DG.add_edge('c', 'd')
DG.add_edge('d', 'e')
DG.add_edge('c', 'f')
DG.add_edge('f', 'a')
DG.add_edge('e', 'c')
DG.add_edge('b', 'e')

a = natural_loops(DG)
print('----')
b = cycle_method(DG)
print('----')
print('natural loops:', a)
print(' cycle method:', b)
assert a-b == set('d')
#nx_draw('./nat_loop_vs_cycle.png', DG)
