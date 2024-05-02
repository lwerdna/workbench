#!/usr/bin/env python

import networkx as nx

G = nx.DiGraph()
# nodes and edges have associated attributes/data

# they can be specified when they're ADDED to the graph:
G.add_node('A', stringdata="one", intdata=1)             # using named parameters
G.add_node('B', **{'stringdata':'two', 'intdata':2})       # using dict

G.add_edge('A', 'B', stringdata='three', intdata=3)       # using named parameters
G.add_edge('B', 'A', **{'stringdata':'four', 'intdata':4}) # using dict

# node data: access and modify, like a dict
print(G.nodes['A'])
G.nodes['A']['stringdata'] = 'nine'
G.nodes['A']['intdata'] = 9
print(G.nodes['A'])

print('--')

# edge data: access and modify, like a dict
breakpoint()
print(G.edges['A','B'])
G.edges['A','B']['stringdata'] = 'twelve'
G.edges['A','B']['intdata'] = 12
print(G.edges['A','B'])

# save/load graphs
nx.write_adjlist(G, 'saved.graph')
G = nx.read_adjlist(fpath, create_using=nx.DiGraph)

# successors() gets child nodes
#  (AKA: neighbors() for undirected graph)
G.successors(source_node)

# ancestors() gets all nodes having a path TO source
nx.ancestors(G, source_node)

# descendants() gets all nodes having a path FROM source
nx.descendants(G, source_node)

# write dot in a pinch
def get_dot(G):
    fp = io.StringIO()
    nx.drawing.nx_pydot.write_dot(G, fp)
    fp.seek(0)
    return fp.read()
