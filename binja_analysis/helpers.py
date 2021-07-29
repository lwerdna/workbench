import binaryninja
from binaryninja import core
from binaryninja import binaryview

from colorama import Fore, Back, Style

import os, sys, re

#------------------------------------------------------------------------------
# misc
#------------------------------------------------------------------------------

def bbid(bb):
    return 'b%d' % bb.index

def bbtext(bb):
    return '\n'.join(
        ['%08X: %s' % (l.address, l) for l in bb.get_disassembly_text()]
    )

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
        (addr, rest) = re.match(r'^([a-hA-H0-9]{8}): (.*)$', line).group(1,2)
        print('%s%s: %s%s' % (Style.DIM, addr, Style.RESET_ALL, rest))

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

def graph_func(fname, func, reds=[], greens=[], blues=[]):
    attrs = []
    edges = []

    # write attributes
    for bb in func.basic_blocks:
        label = '\\l'.join(['; '+bbid(bb)] + bbtext(bb).split('\n')) + '\\l'
        color = 'black'
        if bb in reds: color='red'
        if bb in greens: color='green'
        if bb in blues: color='blue'
        attrs.append('%s [shape=box color=%s fontname="Courier" label="%s"];' % (bbid(bb), color, label))

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
