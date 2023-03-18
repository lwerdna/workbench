#!/usr/bin/env python

import os
import sys
import re
import random
import readline

from memvm import MemVM

from ctypes import *

# must match CORE_MEM_SZ in gofer
CORE_MEM_SZ = 1024*1024

def edge_label_action(G, a, b):
    action = G.edges[a,b]['action']
    return [f'label="{action}"']

if __name__ == '__main__':
    import networkx as nx
    import curiousbits.graphs.nxtools as nxt
    G = nx.read_gml('input.gml')

    print('')
    print('// ADD ALL NODES, INITIALLY INVISIBLE')
    for n in G.nodes:
        print(f'ADD_NODE({n})')
        print(f'SET_NODE_PROPERTY({n}, "shape", "none")')
        #print(f'SET_NODE_PROPERTY({n}, "shape", "box")')
        print(f'SET_NODE_PROPERTY({n}, "image", "/tmp/image_{n}.png")')
        print(f'SET_NODE_PROPERTY({n}, "style", "invis")')
        if n == 'root':
            print(f'SET_NODE_LABEL({n}, " ")')

    print('')
    print('// ADD ALL EDGES, INITIALLY INVISIBLE')
    for (a,b) in G.edges:
        print(f'ADD_EDGE({a}, {b})')
        print(f'SET_EDGE_PROPERTY({a}, {b}, "style", "invis")')
        action = G.edges[a,b]['action']
        print(f'SET_EDGE_LABEL({a}, {b}, "{action}")')
    print(f'NEXT_FRAME()')

    def traverse_pre(G, root):
        result = [root]
        for c in G.successors(root):
            result.extend(traverse_pre(G, c))
        return result

    nodes = traverse_pre(G, 'root')
    for n in nodes:
        mvm = MemVM()

        if n == 'root':
            print('// MAKE NODE VISIBLE')
            print(f'SET_NODE_PROPERTY({n}, "style", "")')
            if not os.path.exists('/tmp/image_root.png'):
                mvm.snap('/tmp/image_root.png', 64, 64)
            print(f'NEXT_FRAME()')
            del mvm
            continue

        assert len(G.in_edges(n)) == 1
        predecessor = list(G.in_edges(n))[0][0]

        print(f'HIGHLIGHT_NODE({predecessor})')
        print(f'NEXT_FRAME()')

        # actions
        paths = list(nx.all_simple_paths(G, 'root', n))
        assert len(paths) == 1
        path = paths[0]
        actions = [G.edges[a,b]['action'] for a,b in zip(path, path[1:])]

        print(f'SET_EDGE_PROPERTY({predecessor}, {n}, "style", "")')
        print(f'HIGHLIGHT_EDGE({predecessor}, {n})')
        print(f'NEXT_FRAME()')


        print(f'// performing actions: {actions}')
        for action in actions:
            print(f'// performing action: {action}')
            if m := re.match(r'^A(.*)$', action):
                amount = int(m.group(1), 16)

                #if amount == 0x125400:
                #    mvm.set_backend_verbose()
                #    breakpoint()
                mvm.malloc(amount)
            elif m := re.match(r'^F(.*)$', action):
                index = int(m.group(1))
                mvm.free_index(index)
            else:
                print(f'WTF: {action}')

        fpath = f'/tmp/image_{n}.png'
        if not os.path.exists(fpath):
            mvm.snap(fpath, 64, 64)

        print(f'SET_NODE_PROPERTY({n}, "style", "")')
        print(f'UNHIGHLIGHT_NODE({predecessor})')
        print(f'UNHIGHLIGHT_EDGE({predecessor}, {n})')
        print(f'NEXT_FRAME()')

        #print(actions)
        #print(f'{edge[0]}->{edge[1]} uses actions {actions}')

        del mvm

    #print(traverse_pre(G, 'root'))

