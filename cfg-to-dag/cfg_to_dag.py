import os, sys
from pprint import pprint

import networkx as nx

import binaryninja

#------------------------------------------------------------------------------
# LOOP DETECTION
#------------------------------------------------------------------------------

# return list for each loops
# each loop is a list of basic blocks
# eg:
# [[b0,b1,b2], [b7,b8,b9]] means two loops, the first with {b0,b1,b2}, the second with {b7,b8,b9}
def calculate_natural_loops(func):
    loops = []

    # find back edges (B -> A when A dominates B)
    # A is called "header", B is called "footer"
    #
    # WARNING:
    #   Basic_block.back_edge is a less strict "edge to ancestor" definition of back edge.
    #   We need the stricter "edge to dominator" definition for loop detection.
    back_edges = []
    for bb in func.basic_blocks:
        for edge in bb.outgoing_edges:
            if edge.target in edge.source.dominators:
                back_edges.append(edge)
                #print('back edge %s -> %s' % (bbstr(edge.source), bbstr(edge.target)))

    # reverse breadth-first search from footer to header, collecting all nodes
    for edge in back_edges:
        (header, footer) = (edge.target, edge.source)
        #print('collecting blocks for loop fenced between %s and %s:' % (bbstr(header), bbstr(footer)))
        loop_blocks = set([header, footer])
        if header != footer:
            queue = [edge.source]
            while queue:
                cur = queue.pop(0)
                loop_blocks.add(cur)
                new_batch = [e.source for e in cur.incoming_edges if (not e.source in loop_blocks)]
                #print('incoming blocks to %s: %s' % (bbstr(cur), [bbstr(x) for x in new_batch]))
                queue.extend(new_batch)
        #print(','.join([bbstr(n) for n in loop_blocks]))

        # store this loop
        loops.append(list(loop_blocks))

    return loops

#------------------------------------------------------------------------------
# BUILD NETWORKX GRAPHS FROM BINJA FUNCS
#------------------------------------------------------------------------------

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

#------------------------------------------------------------------------------
# COLLAPSE LOOPS
#------------------------------------------------------------------------------

class Binary():
    def __init__(self, fpath):
        self.bview = binaryninja.open_view(fpath)
        assert self.bview

    def bbid(self, bb):
        return f'block@{bb.start:X}'

    # get a function's control flow graph
    def get_cfg(self, func_name):
        func = self.bview.get_functions_by_name(func_name)[0]
        assert func

        G = nx.DiGraph()

        for src in func.basic_blocks:
            G.add_node(self.bbid(src))

            for dst in [edge.target for edge in src.outgoing_edges]:
                G.add_node(self.bbid(dst))
                G.add_edge(self.bbid(src), self.bbid(dst))
        
        return G

    # get a function's control flow graph as a DAG by collapsing loop blocks
    def get_cfg_dag(self, func_name):
        func = self.bview.get_functions_by_name(func_name)[0]
        assert func

        # collect all loop blocks
        all_loop_blocks = set()
        nat_loops = calculate_natural_loops(func)
        for (i,loop) in enumerate(nat_loops):
            #print('loop%d has %d blocks: %s' % (i, len(loop), loop))
            all_loop_blocks.update(loop)

        # consolidate loops, two cases I can think of:
        # one loop is within another
        # two loops share _some_ of their blocks
        seen_so_far = set()
        consolidated_loops = []
        for (i,loop) in enumerate(nat_loops):
            searched = dfs_clamped(loop[0], all_loop_blocks, seen_so_far)
            #print('loop%d has %d blocks: %s' % (i, len(searched), searched))
            seen_so_far.update(searched)
            if searched:
                consolidated_loops.append(searched)

        # create mapping to replacement nodes
        block2loop = {}
        for (i,loop) in enumerate(consolidated_loops):
            name = 'loop@%X' % min(b.start for b in loop)
            for block in loop:
                block2loop[block] = name

        #pprint(block2loop)

        # create networkX graph
        G = nx.DiGraph()

        for src in func.basic_blocks:
            label_src = block2loop.get(src, self.bbid(src))
            if label_src.startswith('loop'):
                #breakpoint()
                pass
            G.add_node(label_src)

            for dst in [edge.target for edge in src.outgoing_edges]:
                label_dst = block2loop.get(dst, self.bbid(dst))

                # skip intra-loop edges
                if label_src == label_dst:
                    #print(f'skipping {label_src}->{label_dst}')
                    continue

                G.add_node(label_dst)
                #print(f'adding {label_src} to {label_dst}')
                G.add_edge(label_src, label_dst)

        return G

