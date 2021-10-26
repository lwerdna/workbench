#!/usr/bin/env python

# draw loops (and subloops) with graphviz subgraphs / graph clustering

import sys, pprint
from helpers import *

# these are nodes in a subgraph hierarchy
#
# where near-root nodes are supersets, children are subsets
#
class SNode():
    def __init__(self, set_=None, children=None):
        if set_ == None:
            set_ = set()
        if children == None:
            children = []
        self.set_ = set_
        self.children = children

    def insert(self, new_set):
        # CASE0: incoming set is the superset of one or more children
        subset_idxs = []
        for (i,child) in enumerate(self.children):
            if new_set > child.set_:
                subset_idxs.append(i)

        if subset_idxs:
            new_children = []
            for idx in sorted(subset_idxs, reverse=True):
                new_children.append(self.children.pop(idx))
            self.children.append(SNode(new_set, new_children))
            return self

        # CASE1: incoming set is the subset of a child
        superset_idxs = []
        for (i,child) in enumerate(self.children):
            if new_set < child.set_:
                superset_idxs.append(i)
        assert len(superset_idxs) in [0,1]

        if superset_idxs:
            self.children[superset_idxs[0]] = self.children[superset_idxs[0]].insert(new_set)
            return self

        # CASE2: incoming set is simply a new sibling
        self.children.append(SNode(new_set, []))
        return self

    def check(self):
        if self.set_:
            for child in self.children:
                assert self.set_ > child.set_

        for child in self.children:
            child.check()

    def subgraph(self, depth=0):
        dummy_root = not bool(self.set_)

        indent = '    '*depth
        indent2 = '    '*(depth+1)
        result_lines = []

        if not dummy_root:
            # collect blocks that will be handled by recursive calls
            child_blocks = set()
            for child in self.children:
                 child_blocks = child_blocks.union(child.set_)

            # collect edges
            subgraph_edges = []
            subgraph_escapes = []
            for src in self.set_:
                for dst in [edge.target for edge in src.outgoing_edges]:
                    if src in child_blocks:
                        continue
                    elif dst in self.set_:
                        subgraph_edges.append((src, dst))
                    else:
                        subgraph_escapes.append((src, dst))

            cluster_id = 'loop' + '_'.join(sorted([bbid(bb) for bb in self.set_]))

            # print edges that leave the subgraph
            result_lines.append('%s// %s edges that leave the cluster' % (indent, cluster_id))
            for (src, dst) in subgraph_escapes:
                result_lines.append(indent + '%s -> %s;' % (bbid(src), bbid(dst)))

            # print the subgraph
            result_lines.append('%s// cluster' % (indent))
            result_lines.append(indent + 'subgraph cluster_%s {' % cluster_id)
            result_lines.append(indent2 + 'pencolor=black;')
            result_lines.append(indent2 + 'bgcolor="#' + ('%02x'%(0xe0-0x10*depth))*3 +'";')
            for (src, dst) in subgraph_edges:
                result_lines.append(indent2 + '%s -> %s;' % (bbid(src), bbid(dst)))

        for child in self.children:
            result_lines.extend(child.subgraph(depth+1))

        if not dummy_root:
            result_lines.append(indent + '}')

        return result_lines

    def str_helper(self, depth):
        result = []
        if self.set_:
            result.append('    '*depth + ','.join([bbid(x) for x in self.set_]))
        for child in self.children:
            result.extend(child.str_helper(depth+1))
        return result

    def __str__(self):
        lines = self.str_helper(0)
        return '\n'.join(lines)

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func_name = '_some_loops' if not sys.argv[2:] else sys.argv[2]

    (bv, func) = quick_get_func(fpath, func_name)
    if not bv:
        raise Exception('BINJA didnt return analysis on -%s-' % fpath)

    funcs = [func]
    if not func or func_name == 'all':
        funcs = bv.functions

    for func in funcs:
        print('-------- analyzing function %s --------' % func.name)

        # loops is like [[b0,b1], [b3,b4,b5], ...]
        loops = calculate_natural_loops(func)
        for loop in loops:
            print('loop: ' + ','.join(bbid(x) for x in loop))

        loop_hierarchy = SNode()
        print('loop hierarchy at start:')
        print(loop_hierarchy)

        all_loop_blocks = set()
        for loop in [set(l) for l in loops]:
            all_loop_blocks = all_loop_blocks.union(loop)
            loop_hierarchy.insert(set(loop))

        print('loop hierarchy:')
        print(loop_hierarchy)

        attrs = []
        edges = []

        # write attributes
        for bb in func.basic_blocks:
            label = '\\l'.join(['; '+bbid(bb)] + bbtext(bb).split('\n')) + '\\l'
            label = label.replace('\\n', '\\\\n')
            label = label.replace('"', '\\"')
            attrs.append('    %s [style="filled" shape=box color=black fillcolor=white fontname="Courier" fontsize=10 label="%s"];' % (bbid(bb), label))

        # write NON-LOOP edges
        for src in [bb for bb in func.basic_blocks]:
            if src in all_loop_blocks:
                continue
            for dst in [edge.target for edge in src.outgoing_edges]:
                edges.append('    %s -> %s;' % (bbid(src), bbid(dst)))

        # write LOOP edges (in clusters)
        subgraphs = loop_hierarchy.subgraph()

        dot = []
        dot.append('digraph G {')
        dot.extend(edges)
        dot.extend(subgraphs)
        dot.extend(attrs)
        dot.append('}')

        #print('\n'.join(dot))

        with open('/tmp/tmp.dot', 'w') as fp:
            fp.write('\n'.join(dot))

        output_png = '%s.png' % func.name
        print('writing /tmp/%s' % output_png)
        os.system('dot /tmp/tmp.dot -Tpng -o /tmp/%s' % output_png)
        #os.system('open /tmp/%s' % output_png)
