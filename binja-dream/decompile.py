#!/usr/bin/env python

import os
import sys
import re
from subprocess import Popen, PIPE

import z3
import sympy
import networkx as nx
import binaryninja
from binaryninja.enums import *
from binaryninja import lowlevelil

import symstate
from helpers import pretty_print_z3

from pprint import pprint

SVG_SCALE = .6

def shellout(cmd, input_text=None):
    process = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE)
    if input_text == None:
        (stdout, stderr) = process.communicate()
    else:
        if type(input_text) == str:
            input_text = input_text.encode('utf-8')
        (stdout, stderr) = process.communicate(input=input_text)
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    process.wait()
    return (stdout, stderr)

###############################################################################
# BASIC BLOCK UTILITIES
###############################################################################

def bbid(bb):
    #if not type(bb) in [
    #    binaryninja.basicblock.BasicBlock,
    #    binaryninja.lowlevelil.LowLevelILBasicBlock,
    #    binaryninja.mediumlevelil.MediumLevelILBasicBlock,
    #    binaryninja.highlevelil.HighLevelILBasicBlock
    #]:
    #    raise Exception(f'ERROR: how to get block id for {type(bb)}')

    #return 'b%d' % bb.index

    return bb.index

# returns the text header of a given block
# "b3 [0x100003a60, 0x100003a78)"
def bbhdr_min(bb):
    return f'{bb.index}'

def bbhdr_full(bb):
    if type(bb) == binaryninja.basicblock.BasicBlock:
        return '; b%d [0x%X, 0x%X)' % (bb.index, bb.start, bb.end)
    else:
        return '; b%d [%d, %d)' % (bb.index, bb.start, bb.end)

# returns the text body of a given block
def bbtext_min(bb):
    return ''

def bbtext_full(bb):
    lines = []
    #lines.append('%s:' % bbid(bb))
    lines.extend(['%08X: %s' % (l.address, l) for l in bb.get_disassembly_text()])
    return '\n'.join(lines)

###############################################################################
# BASIC BLOCK UTILITIES
###############################################################################

def nx2dot(G):
    dot = []
    dot.append('digraph G {')

    # global graph settings
    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')
    #dot.append('node [shape="rectangle"];')
    #dot.append('node [shape="rectangle" fontname="Courier New" fontsize="8"];')
    #dot.append('edge [fontname="Courier New" fontsize="8"];')

    # node list
    dot.append('// nodes')
    for n in G.nodes:
        dot.append(f'{n} [label="{n}"];')

    # edge list
    dot.append('// edges')
    for (n0,n1) in G.edges:
        data = G.edges[n0,n1]

        attrs = []

        # compute label
        if 'tag' in data:
            label = str(data['tag'])
            attrs.append(f'label="{label}"')

        # compute color
        lookup = { BranchType.TrueBranch:'darkgreen',
                   BranchType.FalseBranch:'darkred',
                   BranchType.UnconditionalBranch:'darkblue' }
        if color := lookup.get(data.get('btype'), 'black'):
            attrs.append(f'color="{color}"')

        dot.append(f'{n0} -> {n1} [' + ' '.join(attrs) + '];')

    dot.append('}')

    return '\n'.join(dot)

def dot_to_svg_obj(dot):
    global SVG_SCALE
    stdout, stderr = shellout(['dot', '-Tsvg'], dot)
    if stderr:
        raise Exception(stderr)
    else:
        svg = scale_svg(stdout, SVG_SCALE)
        svg_obj = SVG(data=svg)
        return svg_obj

def draw_basic_blocks_full(func, reds=[], greens=[], blues=[]):
    global SVG_SCALE
    dot = function_to_dot(func, bbhdr_full, bbtext_full, reds, greens, blues)
    return dot_to_svg_obj(dot)

def draw_basic_blocks_min(func, reds=[], greens=[], blues=[]):
    global SVG_SCALE
    dot = function_to_dot(func, bbhdr_min, bbtext_min, reds, greens, blues)
    return dot_to_svg_obj(dot)

def draw_networkx(G, fbase='/tmp/tmp'):
    dot = nx2dot(G)

    finput = fbase+'.dot'
    foutput = fbase+'.png'

    with open(finput, 'w') as fp:
        fp.write(dot)

    cmd = f'dot {finput} -Tpng -o {foutput}'
    print(cmd)
    os.system(cmd)

###############################################################################
# TO
###############################################################################

# convert a Binary Ninja CFG to a NetworkX directed graph
def bn2nx(func):
    G = nx.DiGraph()

    for src in func.basic_blocks:
        G.add_node(bbid(src))

        for edge in src.outgoing_edges:
            a, b = bbid(src), bbid(edge.target)
            G.add_node(b)
            G.add_edge(a, b, btype=edge.type) # BranchType.TrueBranch, BrancType.FalseBranch, etc.

    return G

# computes the slice of the graph with simple paths a -> b
def slice(G, a, b):
    G2 = nx.DiGraph()

    for path in nx.all_simple_paths(G, source=a, target=b):
        for n in path:
            G2.add_node(n)
            # copy node data
            for (k,v) in G.nodes[n].items():
                G2.nodes[n][k] = v

        for (n0, n1) in zip(path, path[1:]):
            G2.add_edge(n0, n1)
            # copy edge data
            for (k,v) in G.edges[n0,n1].items():
                G2.edges[n0,n1][k] = v

    return G2

def is_cond(block):
    instr = block[-1]
    return instr.operation == LowLevelILOperation.LLIL_IF

def get_cond(block, state):
    instr = block[-1]
    if instr.operation == LowLevelILOperation.LLIL_IF:
        # LLIL_IF
        #   LLIL_CMP_X
        #     left_side
        #     right_side
        #   true_block_idx
        #   false_block_idx
        cmp = instr.operands[0]
        return state.llil_to_expr(cmp)
    else:
        return None

# tag conditions
def tag_edges(G, func):
    state = symstate.State(func.arch)

    for n in G.nodes:
        block = func.basic_blocks[n]
        if is_cond(block):
            sym = sympy.symbols(f'c{n}')
            for e in G.out_edges(n):
                # e is a tuple like (3, 5)
                match G.edges[e]['btype']:
                    case BranchType.TrueBranch:
                        G.edges[e]['tag'] = sym
                    case BranchType.FalseBranch:
                        G.edges[e]['tag'] = ~sym
                print(f'edge {e[0]}->{e[1]} tagged {G.edges[e]["tag"]}')

def compute_reaching_conditions(G):
    sort = list(nx.topological_sort(G))

    conds = {n:False for n in G.nodes}
    conds[sort[0]] = True

    for b in sort:
        for a in G.pred[b]:
            tag = G.edges[a,b].get('tag', True)
            conds[b] = conds[b] | (conds[a] & tag)

    pprint(conds)

    print('simplifying...')

    for n in conds:
        conds[n] = sympy.simplify_logic(conds[n])

    pprint(conds)

if __name__ == '__main__':
    # target file and symbol
    fpath = os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/testbins/tests-macos-x64-macho')
    symbol = '_dream_cfg'
    if sys.argv[2:]:
        fpath, symbol = sys.argv[1:3]

    # get llil function
    bv = binaryninja.open_view(fpath)
    func = bv.get_functions_by_name(symbol)[0].llil.ssa_form
    G = bn2nx(func)

    #
    draw_networkx(G, 'phase0-cfg')

    # get R2 region
    R2 = slice(G, 2, 13)
    tag_edges(R2, func)
    draw_networkx(R2, 'R2')

    compute_reaching_conditions(R2)
    breakpoint()

    #draw_networkx(G)

    #bb = func.llil.basic_blocks[0]
    #reds = [bb for bb in func.llil.basic_blocks if bb[-1].operation == LowLevelILOperation.LLIL_IF]
    #draw_basic_blocks_min(func.llil, reds)
