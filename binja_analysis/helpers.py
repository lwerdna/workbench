import binaryninja
from binaryninja import core
from binaryninja import binaryview

from colorama import Fore, Back, Style

import os, sys, re

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
    disassembly_text_lines = bb.get_disassembly_text()
    print(Fore.GREEN, '; b%d: %s has %d instructions' % \
      (bb.index, str(bb), len(disassembly_text_lines)), Style.RESET_ALL)
    for disassembly_text_line in disassembly_text_lines:
        print(Style.DIM, '%08X:' % disassembly_text_line.address, Style.RESET_ALL, end='')
        print('%s' % (str(disassembly_text_line)))

# print function, split into basic blocks
def print_function_disasm(func):
    print(Fore.GREEN, '; %s has %d basic blocks' % (str(func), len(func.basic_blocks)), Style.RESET_ALL)
    for bb in sorted(func.basic_blocks, key=lambda bb: bb.start):
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

def bbname(bb):
    return 'b%d' % bb.index

def graph_func(fname, func, reds=[], greens=[], blues=[]):
    attrs = []
    edges = []

    # write attributes
    for bb in func.basic_blocks:
        if bb in reds:
            attrs.append('%s [color=red];' % bbname(bb))
        if bb in greens:
            attrs.append('%s [color=green];' % bbname(bb))
        if bb in blues:
            attrs.append('%s [color=blue];' % bbname(bb))

    # write edges
    for src in func.basic_blocks:
        for edge in src.outgoing_edges:
            dst = edge.target
            edges.append('%s -> %s;' % (bbname(src), bbname(dst)))

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
