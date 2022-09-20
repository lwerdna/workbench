#!/usr/bin/env python

import os
import sys
import re
from subprocess import Popen, PIPE

from IPython.display import SVG

from bs4 import BeautifulSoup

import networkx as nx

import binaryninja
from binaryninja.enums import *

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
# SVG UTILITIES
###############################################################################

# https://stackoverflow.com/questions/51452569/how-to-resize-rescale-a-svg-graphic-in-an-ipython-jupyter-notebook
def scale_svg(svg, scale=1.0):
    #with open('/tmp/before.svg', 'w') as fp:
    #    fp.write(svg.encode('utf-8'))

    soup = BeautifulSoup(svg, features='xml')

    svg_elem = soup.find("svg")
    w = svg_elem.attrs["width"].rstrip("pt")
    h = svg_elem.attrs["height"].rstrip("pt")

    ws = float(w)*scale
    hs = float(h)*scale

    svg_elem.attrs["width"] = f"{ws}pt"
    svg_elem.attrs["height"] = f"{hs}pt"
    svg_elem.attrs["viewBox"] = f"0.00 0.00 {ws} {hs}"

    # <g id="graph0" class="graph" transform="scale(1 1) rotate(0) translate(4 672)">
    # to
    # <g id="graph0" class="graph" transform="scale(.5 .5) rotate(0) translate(4 672)">
    g_elt = svg_elem.find("g")
    tf = g_elt.attrs["transform"]
    tf2 = re.sub(
        "scale\(.*?\)",
        f"scale({scale} {scale})",
        tf
    )
    g_elt.attrs["transform"] = tf2

    svg = str(svg_elem)

    #with open('/tmp/after.svg', 'w') as fp:
    #    fp.write(svg.encode('utf-8'))

    return svg

def scale_svg_obj(svg_obj, scale=1.0):
    svg.data = scale_svg(svg.data) 

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

def function_to_dot(func, bbhdr, bbtext, reds=[], greens=[], blues=[]):
    attrs = []
    edges = []

    # write attributes
    for bb in func.basic_blocks:
        label_lines = [bbhdr(bb)]
        if text := bbtext(bb):
            label_lines.extend(text.split('\n'))
            label_lines.append('\\l')
        label = '\\l'.join(label_lines)
        label = label.replace('\\n', '\\\\n')
        label = label.replace('"', '\\"')
        color = 'black'
        if bb in reds: color='red'
        if bb in greens: color='green'
        if bb in blues: color='blue'
        shape_attr = 'shape=box '
        shape_attr = ''
        attrs.append(f'{bbid(bb)} [{shape_attr}color={color} fontname="Courier" fontsize=10 label="{label}"];')

    # write edges
    for src in func.basic_blocks:
        for edge in src.outgoing_edges:
            dst = edge.target
            edges.append('%s -> %s;' % (bbid(src), bbid(dst)))

    dot = []
    dot.append('digraph G {')
    dot.extend(edges)
    dot.extend(attrs)
    dot.append('}')
    return '\n'.join(dot)

def nx2dot(G):
    if 0:
        # can't figure out how to get edge labels to draw
        source = nx.drawing.nx_pydot.to_pydot(G).create_svg()
        svg = scale_svg(source, SVG_SCALE)
        svg_obj = SVG(data=svg)
        return svg_obj
    
    dot = []
    dot.append('digraph G {')
    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')
    #dot.append('node [shape="rectangle"];')
    #dot.append('node [shape="rectangle" fontname="Courier New" fontsize="8"];')
    #dot.append('edge [fontname="Courier New" fontsize="8"];')
    dot.append('// nodes')
    for n in G.nodes:
        dot.append(f'{n} [label="{n}"];')
    dot.append('// edges')
    for (n0,n1) in G.edges:
        label = G.get_edge_data(n0, n1).get('label', '')
        dot.append(f'{n0} -> {n1} [label="{label}"];')
    dot.append('}')
    breakpoint()
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

def draw_networkx(G):
    dot = nx2dot(G)
    return dot_to_svg_obj(dot)

###############################################################################
# TO
###############################################################################

# convert a Binary Ninja CFG to a NetworkX directed graph
def bn2nx(func):
    G = nx.DiGraph()

    for src in func.basic_blocks:
        G.add_node(bbid(src))

        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_node(bbid(dst))
            #G.add_edge(bbid(src), bbid(dst), label=f'{bbid(src)} -> {bbid(dst)}')
            G.add_edge(bbid(src), bbid(dst))
            breakpoint()

    return G

# computes the slice of the graph with simple paths a -> b
def cfg_slice(func, a, b):
    G = bn2nx(func)
    G2 = nx.DiGraph()
    for path in nx.all_simple_paths(G, source=bbid(a), target=bbid(b)):
        for n in path:
            G2.add_node(n)
        for (n0, n1) in zip(path, path[1:]):
            G2.add_edge(n0, n1, label=G.get_edge_data(n0, n1).get('label', ''))

    return G2

if __name__ == '__main__':
    fpath = os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/testbins/tests-macos-x64-macho')
    bv = binaryninja.open_view(fpath)
    func = bv.get_functions_by_name('_dream_cfg')[0]
    llil = func.llil

    G = cfg_slice(llil, llil.basic_blocks[15], llil.basic_blocks[11])
    draw_networkx(G)

    bb = func.llil.basic_blocks[0]
    reds = [bb for bb in func.llil.basic_blocks if bb[-1].operation == LowLevelILOperation.LLIL_IF]
    draw_basic_blocks_min(func.llil, reds)
