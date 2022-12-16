#!/usr/bin/env python

import os
import sys
import re
import random
import readline

from PIL import Image

from ctypes import *

# must match CORE_MEM_SZ in gofer
CORE_MEM_SZ = 1024*1024

def rgb_hex_to_tuple(h):
    return (h>>16, (h>>8)&0xFF, h&0xFF)

def edge_label_action(G, a, b):
    action = G.edges[a,b]['action']
    return [f'label="{action}"']


if __name__ == '__main__':
    mvm = MemVM()
    print(mvm)

    while 1:
        inp = input('SHELL> ')

        if inp == 'quit':
            break

        elif m := re.match(r'^malloc (.*)$', inp):
            size = m.group(1)
            size = int(size, 10 if size.isdigit() else 16)
            addr = mvm.malloc(size)
            print(f'allocated 0x{size:X} bytes at 0x{addr:X}')

        elif m := re.match(r'^free (.*)$', inp):
            addr = m.group(1)
            addr = int(addr, 16)
            mvm.free(addr)
            print(f'free\'d buffer at 0x{addr:X}')

        elif m := re.match(r'^fill', inp):
            size = 1
            while True:
                result = mvm.malloc(size)
                if result == None:
                    print(f'filled')
                    break
                size *= 2

        elif inp in ['pic', 'picture']:
            mvm.snap('/tmp/tmp.png')
            os.system('open /tmp/tmp.png')

        elif inp == 'fun':
            for i in range(10):
                action = random.choice(['malloc', 'free'])
                match action:
                    # allocate a random buffer
                    case 'malloc':
                        size = random.randint(1*1024, 128*1024)
                        mvm.malloc(size)
                    # free a random buffer
                    case 'free':
                        mvm.free_random()

                print(mvm)
                mvm.snap(f'./frames/frame{i:08d}.png')

            os.system('ffmpeg -r 60 -f image2 -i ./frames/frame%08d.png -vcodec libx264 -crf 25  -pix_fmt yuv420p ./frames/fun.mp4')

        elif inp == 'gen_heap_search':
            def gen_node_name(G):
                return next(x for x in range(1000000) if not x in G.nodes)

            def gen_tree(G, root, depth):
                if depth >= 2:
                    return

                for num_children in range(random.randint(1,3)):
                    child = gen_node_name(G)
                    G.add_node(child)
                    G.add_edge(root, child)
                    print(G)

                    # generate action
                    action, action_type = None, random.choice(['alloc', 'free'])
                    if depth == 0:
                        action_type = 'alloc'
                    if action_type == 'alloc':
                        # alloc one of 7k, 14k, 21k, ..., 240k
                        amount = random.choice([7*i*1024 for i in range(1,21)])
                        #action = f'alloc({amount:X})'
                        action = f'A{amount:X}'
                    else:
                        # free one of the previous alloc'd
                        which = random.choice(range(depth))
                        action = f'free({which})'
                        action = f'F{which}'

                    print('setting action to: ' + action)
                    G.edges[root, child]['action'] = action

                    gen_tree(G, child, depth+1)

            import networkx as nx
            import curiousbits.graphs.nxtools as nxt
            G = nx.DiGraph()
            G.add_node('root')
            gen_tree(G, 'root', 0)

            nx.write_gml(G, 'input.gml')
            nxt.draw(G, '/tmp/input.svg', f_edge_attrs=edge_label_action)

        elif inp == 'movie':
            import networkx as nx
            import curiousbits.graphs.nxtools as nxt
            G = nx.read_gml('input.gml')

            def traverse_pre(G, root):
                result = [root]
                for c in G.successors(root):
                    result.extend(traverse_pre(G, c))
                return result

            nodes = traverse_pre(G, 'root')
            for n in nodes:
                print(f'ADD_NODE({n})')

                mvm = MemVM()

                if n == 'root':
                    print(f'ADD_NODE({n})')
                    print(f'SET_NODE_LABEL({n}, " ")')
                    print(f'NEXT_FRAME()')

                    print(f'SET_NODE_PROPERTY({n}, "image", "/tmp/image_root.png")')
                    mvm.snap('/tmp/image_root.png', 128, 128)
                    print(f'NEXT_FRAME()')

                    continue

                assert len(G.in_edges(n)) == 1
                predecessor = list(G.in_edges(n))[0][0]

                print(f'HIGHLIGHT_NODE({predecessor})')
                print(f'NEXT_FRAME()')

                print(f'ADD_EDGE({predecessor}, {n})')
                print(f'HIGHLIGHT_EDGE({predecessor}, {n})')
                print(f'NEXT_FRAME()')

                # actions
                paths = list(nx.all_simple_paths(G, 'root', n))
                assert len(paths) == 1
                path = paths[0]
                actions = [G.edges[a,b]['action'] for a,b in zip(path, path[1:])]
                print(f'performing actions: {actions}')
                for action in actions:
                    print('A')
                    print(mvm)
                    print(f'performing action: {action}')
                    if m := re.match(r'^A(.*)$', action):
                        amount = int(m.group(1), 16)
                        mvm.malloc(amount)
                    elif m := re.match(r'^F(.*)$', action):
                        pass
                    else:
                        print(f'WTF: {action}')
                    print('B')
                    print(mvm)

                fpath = f'/tmp/image_{n}.png'
                mvm.snap(fpath, 128, 128)
                print(f'SET_NODE_PROPERTY({n}, "image", "{fpath}")')
                print(f'NEXT_FRAME()')

                #print(actions)
                #print(f'{edge[0]}->{edge[1]} uses actions {actions}')

            #print(traverse_pre(G, 'root'))

