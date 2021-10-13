import binaryninja
from binaryninja import core
from binaryninja import binaryview
from binaryninja import BinaryViewType

from colorama import Fore, Back, Style

import networkx as nx
from miasm.core.graph import DiGraph

import os, sys, re, time

#------------------------------------------------------------------------------
# misc
#------------------------------------------------------------------------------

def bbid(bb):
    return 'b%d' % bb.index

def bbtext(bb):
    lines = []
    #lines.append('%s:' % bbid(bb))
    lines.extend(['%08X: %s' % (l.address, l) for l in bb.get_disassembly_text()])
    return '\n'.join(lines)

def quick_get_func(fpath='./tests', symbol='_fizzbuzz'):
    if sys.argv[1:]:
        fpath = sys.argv[1]
    if sys.argv[2:]:
        symbol = sys.argv[2]

    update_analysis = True
    callbacks = None
    options = {'analysis.mode':'controlFlow'}
    #bv = BinaryViewType.get_view_of_file(fpath)
    print('opening %s in binaryninja' % fpath)
    t0 = time.perf_counter()
    bv = binaryninja.open_view(fpath, update_analysis, callbacks, options)
    if not bv:
        raise Exception('binary ninja didnt return analysis on -%s-' % fpath)
    #bv.update_analysis_and_wait()
    #func = bv.get_functions_by_name(symbol)[0]
    t1 = time.perf_counter()
    print('analysis complete after %fs' % (t1-t0))

    func = None
    if symbol:
        funcs = [f for f in bv.functions if f.name==symbol]
        if funcs:
            func = funcs[0]
    #if not funcs:
    #    raise Exception('binary ninja didnt return func on -%s-' % symbol)
    return (bv, func)

#------------------------------------------------------------------------------
# graph calculations
#------------------------------------------------------------------------------

# calculate the depths from the entry block
def calculate_depths(func):
    result = {'b0':0}

    basic_blocks = list(func.basic_blocks)
    queue = [basic_blocks[0]]
    while queue:
        block = queue.pop(0)
        label = bbid(block)
        depth = result[label]
        for edge in block.outgoing_edges:
            if not bbid(edge.target) in result:
                result[bbid(edge.target)] = depth+1
                queue.append(edge.target)
     
    return result

#------------------------------------------------------------------------------
# attempt map between IL levels
#------------------------------------------------------------------------------

#------------------------------------------------------------------------------
# access instrutions at various IL levels by address
#------------------------------------------------------------------------------

def get_instruction_addresses(func):
    addrs = []
    for bb in func.basic_blocks:
        bb._buildStartCache()
        addrs.extend(bb._instStarts)
    return sorted(addrs)

# func: binaryninja.function.Function
#       binaryninja.lowlevelil.LowLevelILFunction
#       binaryninja.mediumlevelil.MediumLevelILFunction
#       binaryninja.highlevelil.HighLevelILFunction
#
def get_function_instruction_by_address(func, addr):
    result = []
    for bb in func.basic_blocks:
        for instr in bb:
            if instr.address == addr:
                result.append(instr)
    return result

# returns [string]
def get_disassembly_at(bv, addr):
    return bv.get_disassembly(addr)

# returns [binaryninja.lowlevelil.LowLevelILInstruction, ...]
def get_lifted_il_at(bv, addr):
    func = bv.get_functions_containing(addr)[0]
    return get_function_instruction_by_address(func.lifted_il, addr)

# returns [binaryninja.lowlevelil.LowLevelILInstruction, ...]
def get_llil_at(bv, addr):
    func = bv.get_functions_containing(addr)[0]
    return get_function_instruction_by_address(func.llil, addr)

# returns [binaryninja.mediumlevelil.MediumLevelILInstruction, ...]
def get_mlil_at(bv, addr):
    func = bv.get_functions_containing(addr)[0]
    return get_function_instruction_by_address(func.mlil, addr)

# returns [binaryninja.highlevelil.HighLevelILInstruction, ...]
def get_hlil_at(bv, addr):
    func = bv.get_functions_containing(addr)[0]
    return get_function_instruction_by_address(func.hlil, addr)

#------------------------------------------------------------------------------
# printing (usually to console) utilities
#------------------------------------------------------------------------------

# python bytes -> BinaryNinja function
def bytes_to_function(data, plat_name='linux-x86_64'):
    bv = binaryview.BinaryView.new(data)

    platform = binaryninja.Platform[plat_name]
    bv.platform = platform
    bv.add_function(0, plat=platform)
    bv.update_analysis_and_wait()

    print_binary_view(bv)
    assert len(bv.functions) == 1
    return bv.functions[0]

# print basic block
def print_basic_block_disasm(bb):
    lines = bbtext(bb).split('\n')

    print('%s; %s: %s has %d instructions' % \
      (Fore.GREEN, bbid(bb), str(bb), len(lines)), Style.RESET_ALL)

    for line in lines:
        m = re.match(r'^([a-hA-H0-9]{8,16}): (.*)$', line)
        if m:
            (addr, rest) = m.group(1,2)
            print('%s%s: %s%s' % (Style.DIM, addr, Style.RESET_ALL, rest))
            continue

        m = re.match(r'^b\d+:$', line)
        if m:
            continue

        breakpoint()

# print function, split into basic blocks
def print_function_disasm(func):
    basic_blocks = list(func.basic_blocks)
    print(Fore.GREEN, '; %s has %d basic blocks' % (str(func), len(basic_blocks)), Style.RESET_ALL)
    for bb in sorted(basic_blocks, key=lambda bb: bb.start):
        print_basic_block_disasm(bb)

# print all functions in a binary view
# binaryview has functions
# functions have basicblocks
def print_binary_view(bv):
    for func in bv.functions:
        print_function_disasm(func)

#------------------------------------------------------------------------------
# graphing utilities
#------------------------------------------------------------------------------

def graph_func(fname, func, reds=[], greens=[], blues=[]):
    attrs = []
    edges = []

    # write attributes
    for bb in func.basic_blocks:
        label = '\\l'.join(['; '+bbid(bb)] + bbtext(bb).split('\n')) + '\\l'
        label = label.replace('\\n', '\\\\n')
        label = label.replace('"', '\\"')
        color = 'black'
        if bb in reds: color='red'
        if bb in greens: color='green'
        if bb in blues: color='blue'
        attrs.append('%s [shape=box color=%s fontname="Courier" fontsize=10 label="%s"];' % (bbid(bb), color, label))

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

    dot_name = '%s.dot' % fname
    if not os.path.exists(dot_name):
        print('writing %s' % dot_name)
        with open(dot_name, 'w') as fp:
            fp.write('\n'.join(dot))
    else:
        print('skipping %s (already exists)' % dot_name)

    png_name = '%s.png' % fname
    if not os.path.exists(png_name):
        print('writing %s' % png_name)
        os.system('dot %s -Tpng -o %s' % (dot_name, png_name))
        #os.system('neato ./cfg.dot -Tpng -o cfg_neato.png')
        #os.system('fdp ./cfg.dot -Tpng -o cfg_fdp.png')
        #os.system('sfdp ./cfg.dot -Tpng -o cfg_sfdp.png')
        #os.system('twopi ./cfg.dot -Tpng -o cfg_twopi.png')
        #os.system('circo ./cfg.dot -Tpng -o cfg_circo.png')
    else:
        print('skipping %s (already exists)' % png_name)

#------------------------------------------------------------------------------
# networkx helpers
#------------------------------------------------------------------------------

# convert a Binary Ninja CFG to a NetworkX directed graph
def nx_graph_from_binja(func):
    G = nx.DiGraph()

    for src in func.basic_blocks:
        G.add_node(bbid(src))

        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_node(bbid(dst))
            G.add_edge(bbid(src), bbid(dst))

    return G

# return the dominators (non-strict) of target
def nx_dominators(G, node_target, node_start='b0'):
    # get dominator tree, parent is immediate dominator
    lookup = nx.immediate_dominators(G, node_start)
    assert node_target in lookup

    # walk up the tree
    result = []
    current = node_target
    while True:
        result.append(current)
        if current == node_start:
            break
        current = lookup[current]

    return result

def nx_draw(path_png, G):
    path_dot = '/tmp/tmp.dot'
    print('writing '+path_dot)
    nx.drawing.nx_pydot.write_dot(G, path_dot) 

    print('writing '+path_png)
    os.system('dot %s -Tpng -o %s' % (path_dot, path_png))

#------------------------------------------------------------------------------
# miasm helpers
#------------------------------------------------------------------------------

# convert a Binary Ninja CFG to a miasm directed graph
def miasm_graph_from_binja(func):
    G = DiGraph()

    for src in func.basic_blocks:
        for dst in [edge.target for edge in src.outgoing_edges]:
            G.add_edge(bbid(src), bbid(dst))

    return G
