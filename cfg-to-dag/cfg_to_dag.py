#!/usr/bin/env python

import os, sys

import binaryninja

from loop_detection import calculate_natural_loops

import networkx as nx

# return a string identifier for a given basic block node
def bbid(bb):
    return 'b%d' % bb.index

# convert a Binary Ninja CFG to a networkx graph
def binja_func_to_networkx_graph(func):
    G = nx.DiGraph()

    for src in func.basic_blocks:
        G.add_node(bbid(src))

        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_node(bbid(dst))
            G.add_edge(bbid(src), bbid(dst))
        
    return G

# draw a networkx graph into a png by exporting to .DOT and invoking graphviz
# pip install pydot
def draw_graph(G, output='/tmp/tmp.png'):
    fpath = '/tmp/tmp.dot'
    print('writing '+fpath)
    nx.drawing.nx_pydot.write_dot(G, fpath) 

    print('writing '+output)
    os.system('dot %s -Tpng -o %s' % (fpath, output))

def dfs_clamped(block, required, banned):
    result = []

    if block in required and block not in banned:
        result.append(block)

    banned.update([block])

    for bb in [e.target for e in block.outgoing_edges]:
        if bb in banned: continue
        if not bb in required: continue
        result.extend(dfs_clamped(bb, required, banned))

    return result

if __name__ == '__main__':
    fpath = '../testbins/tests-macos-x64-macho' if not sys.argv[1:] else sys.argv[1]
    fname = '_some_loops' if not sys.argv[2:] else sys.argv[2]

    bview = binaryninja.open_view(fpath)
    assert bview
    func = bview.get_functions_by_name(fname)[0]

    # collect all loop blocks
    all_loop_blocks = set()
    nat_loops = calculate_natural_loops(func)
    for (i,loop) in enumerate(nat_loops):
        print('loop%d has %d blocks: %s' % (i, len(loop), loop))
        all_loop_blocks.update(loop)

    # consolidate loops, two cases I can think of:
    # one loop is within another
    # two loops share _some_ of their blocks
    seen_so_far = set()
    consolidated_loops = []
    for (i,loop) in enumerate(nat_loops):
        searched = dfs_clamped(loop[0], all_loop_blocks, seen_so_far)
        print('loop%d has %d blocks: %s' % (i, len(searched), searched))
        seen_so_far.update(searched)
        consolidated_loops.append(searched)

    # create mapping to replacement nodes
    block_to_loop_id = {}
    for (i,loop) in enumerate(consolidated_loops):
        for block in loop:
            block_to_loop_id[block] = i

    # create networkX graph
    G = nx.DiGraph()

    for src in func.basic_blocks:
        label_src = block_to_loop_id.get(src, f'{src.index}') 
        G.add_node(label_src)

        for dst in [edge.target for edge in src.outgoing_edges]:
            label_dst = block_to_loop_id.get(src, f'{dst.index}')

            G.add_node(label_dst)
            G.add_edge(label_src, label_dst)

    draw_graph(G)

