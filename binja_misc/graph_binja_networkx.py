#!/usr/bin/env python
#
# given a binary and a function name, get that function's CFG into networkx format
# draw images of that CFG (cfg_disasm.png, cfg_lifted.png, cfg_llil.png, etc.)
#
# example
# ./graph_binja_networkx.py MyTestProgram _main
#
# requirements:
# pip install networkx
# pip install pydot
# apt-get install graphviz

# changelog:
# 2021-08-24 - created

import os, sys, re, pprint

import binaryninja
from binaryninja import core
from binaryninja import binaryview
from binaryninja.binaryview import BinaryViewType

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

if __name__ == '__main__':
    fpath = sys.argv[1]
    symbol = sys.argv[2]

    bv = BinaryViewType.get_view_of_file(fpath)
    bv.update_analysis_and_wait()

    funcs = bv.get_functions_by_name(symbol)
    if not funcs:
        raise Exception('no functions returned with that name')
    func = funcs[0]

    G = binja_func_to_networkx_graph(func)
    draw_graph(G, './cfg_disasm.png')

    G = binja_func_to_networkx_graph(func.lifted_il)
    draw_graph(G, './cfg_lifted.png')

    G = binja_func_to_networkx_graph(func.llil)
    draw_graph(G, './cfg_llil.png')

    G = binja_func_to_networkx_graph(func.mlil)
    draw_graph(G, './cfg_mlil.png')

    G = binja_func_to_networkx_graph(func.mlil)
    draw_graph(G, './cfg_hlil.png')
