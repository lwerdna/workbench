#!/usr/bin/env python

import os
import sys
import networkx as nx

def nx2dot(G):
    dot = []
    dot.append('digraph G {')
    for (a,b) in G.edges:
        dot.append(f'{a} -> {b}')
    dot.append('}')
    return '\n'.join(dot)

def draw(G, fpath):
    dot = nx2dot(G)
    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write(dot)
    cmd = f'dot /tmp/tmp.dot -Tsvg -o {fpath}'
    os.system(cmd)

def reversed_graph(G):
    T = nx.DiGraph()
    for (a,b) in G.edges():
        T.add_edge(b, a)
    return T

# compute the dominator tree of a single-entry single-successor CFG
def dominator_tree(G):
    T = nx.DiGraph()

    dzeros = [n for n in G.nodes if G.in_degree(n) == 0]
    assert len(dzeros) == 1
    root = dzeros[0]

    for (b, a) in nx.immediate_dominators(G, root).items():
        T.add_node(b)
        T.nodes[b]['label'] = G.nodes[b].get('label', str(b))

        if a == b:
            continue

        T.add_edge(a, b)

    return T

def compute_converge_points(G):
    rgraph = reversed_graph(G)
    dtree = dominator_tree(rgraph)
    return {b:a for (a,b) in dtree.edges}

if __name__ == '__main__':
    if sys.argv[1:]:
        fpath = sys.argv[1]

    G = nx.read_adjlist(fpath, create_using=nx.DiGraph)

    cpoints = compute_converge_points(G)
    for (a,b) in cpoints.items():
        if len(G[a]) < 2:
            continue
        print(f'paths from {a} converge at {b}')

