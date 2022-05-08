#!/usr/bin/env python

import os, sys

import networkx as nx

import cfg_to_dag

# draw a networkx graph into a png by exporting to .DOT and invoking graphviz
# pip install pydot
def draw_graph(G, output='/tmp/tmp.png'):
    fpath = '/tmp/tmp.dot'
    print('writing '+fpath)
    nx.drawing.nx_pydot.write_dot(G, fpath) 

    print('writing '+output)
    os.system('dot %s -Tpng -o %s' % (fpath, output))

if __name__ == '__main__':
    fpath = '../testbins/tests-macos-x64-macho' if not sys.argv[1:] else sys.argv[1]
    function = '_some_loops' if not sys.argv[2:] else sys.argv[2]

    binary = cfg_to_dag.Binary(fpath)

    G = binary.get_cfg(function)
    draw_graph(G, '/tmp/cfg.png')

    G = binary.get_cfg_dag(function)
    draw_graph(G, '/tmp/collapsed.png')
