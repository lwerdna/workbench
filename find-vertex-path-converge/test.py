#!/usr/bin/env python

import os
import sys
import networkx as nx

import logic

def nx2dot(G):
    dot = []
    dot.append('digraph G {')
    dot.append('\t// global settings')
    dot.append('\tgraph [rankdir="LR"]')
    dot.append('\t// nodes')
    for n in G.nodes:
        label = G.nodes[n].get('label', str(n))
        dot.append(f'{n} [label="{label}"];')
    dot.append('\t// edges')
    for (a,b) in G.edges:
        dot.append(f'\t{a} -> {b}')
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

def compute_dominators(G):
    T = dominator_tree(G)

    result = {}
    for dominator in T.nodes:
        for dominatee in nx.descendants(T, dominator):
            result[dominatee] = result.get(dominatee, []) + [dominator]

    return result

def compute_postdominators(G):
    return compute_dominators(reversed_graph(G))

def gen_logic(G):
    # STEP1: tag edges with reaching condition transmitted
    # before: foo -----> bar
    #  after: foo --A--> bar
    var_i = 0
    variables = [logic.VarNode(name) for name in list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')]
    lookup = {}
    for node in nx.topological_sort(G):
        if G.out_degree(node) == 2:
            edges = list(G.out_edges(node))
            assert len(edges) == 2
            G.nodes[node]['varname'] = variables[var_i].name
            G.edges[edges[0]]['tag'] = variables[var_i]
            G.edges[edges[1]]['tag'] = logic.NotNode(variables[var_i])
            var_i += 1

    # compute reaching condition
    sort = list(nx.topological_sort(G))
    conds = {n:logic.ValNode(False) for n in G.nodes}
    conds[sort[0]] = logic.ValNode(True)

    # STEP2:
    # for all a -----> b
    # b's condition is the "OR" of all a's condition "AND" its edge tag
    for b in sort:
        for a in G.pred[b]:
            tag = G.edges[a,b].get('tag', logic.ValNode(True))
            conds[b] = logic.OrNode(conds[b], logic.AndNode(conds[a], tag))

    for (node, expr) in conds.items():
        G.nodes[node]['reaching_condition'] = expr.prune_vals()

if __name__ == '__main__':
    if sys.argv[1:]:
        fpath = sys.argv[1]

    G = nx.read_adjlist(fpath, create_using=nx.DiGraph)

    # generated0.graph -> generated0.svg
    draw(G, fpath.replace('.graph', '.svg'))

    # generate reaching conditions
    gen_logic(G)
    for n in G:
        G.nodes[n]['label'] = f'{n}:\\l' + str(G.nodes[n]['reaching_condition'])
    draw(G, fpath.replace('.graph', '-logic.svg'))

    # OPTION 1/3: simplify at join/converge point
    if 0:
        lookup = {}
        cpoints = compute_converge_points(G)
        for (a,b) in cpoints.items():
            if len(G[a]) < 2:
                continue
            #print(f'paths from {a} converge at {b}')
            varname = G.nodes[a]['varname']
            #print(f'setting {a}\'s variable {varname} to omnitrue at {b}')
            lookup[b] = lookup.get(b, []) + [varname]

    # OPTION 2/3: simplify at all postdominators
    if 0:
        for (a, postdoms) in compute_postdominators(G).items():
            varname = G.nodes[a].get('varname')
            if not varname:
                continue

            for b in postdoms:
                print(f'setting {a}\'s variable {varname} to omnitrue at {b}')
                lookup[b] = lookup.get(b, []) + [varname]

    # OPTION 3/3: simplify at converge point and all descendants
    if 1:
        lookup = {}
        cpoints = compute_converge_points(G)
        for (a, cpoint) in cpoints.items():
            varname = G.nodes[a].get('varname')
            if not varname:
                continue

            #print(f'{a} converges at {cpoint}')
            queue = {cpoint}.union(nx.descendants(G, cpoint))
            #print(f'which expands to {queue}')

            for b in queue:
                print(f'setting {a}\'s variable {varname} to omnitrue at {b}')
                lookup[b] = lookup.get(b, []) + [varname]


    #
    for (node, vnames) in lookup.items():
        print(f'node {node} will have {vnames} set to omnitrue')

        expr = G.nodes[node]['reaching_condition']
        print(expr)
        expr = expr.omnitrue(vnames)
        expr = expr.prune_vals()
        G.nodes[node]['reaching_condition'] = expr

        print(expr)

    #
    for n in G:
        G.nodes[n]['label'] = G.nodes[n]['reaching_condition']    
    draw(G, fpath.replace('.graph', '-reduced.svg'))
