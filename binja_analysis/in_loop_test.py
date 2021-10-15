#!/usr/bin/env python

# test binja's basic block .in_loop field by comparison against miasm

import sys

import binaryninja
from miasm.core.graph import DiGraph

def bbid(bb):
    return 'b%d' % bb.index

def miasm_graph_from_binja(func):
    G = DiGraph()

    for src in func.basic_blocks:
        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_edge(bbid(src), bbid(dst))

    return G

bv = binaryninja.open_view(sys.argv[1], True, None, {'analysis.mode':'controlFlow'})

for func in bv.functions:
    print('-------- analyzing function %s --------' % func.name)

    # get binja's answer
    #
    answer_binja = set()
    for bb in func.basic_blocks:
        if bb.in_loop:
            answer_binja.add(bbid(bb))
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

        raise Exception('FAIL!')
