#!/usr/bin/env python

import os, sys

import binaryninja

def block_id(bb):
    return 'b%d' % bb.index

def block_label(bb):
    lines = []
    addr = bb.start
    for (toks, length) in bb:
        lines.append('%08X: %s' % (addr, ''.join([t.text for t in toks])))
        addr += length
    return '<br>'.join(lines)

def func_to_mermaid(func):
    result = ['graph TD']

    # block identifiers and labels
    for block in func.basic_blocks:
        label = block_label(block).replace('"', '&quot;')
        result.append('\t%s["%s"]' % (block_id(block), label))

    # block identifier to block identifier
    for src in func.basic_blocks:
        for edge in src.outgoing_edges:
            dst = edge.target
            result.append('\t%s --> %s' % (block_id(src), block_id(dst)))

    return '\n'.join(result)

if __name__ == '__main__':
    fpath = '../testbins/tests-linux-x64-elf'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    sym_name = 'collatz_message'
    if sys.argv[2:]:
        sym_name = sys.argv[2]
    sym_name = sym_name.lower()

    with binaryninja.open_view(fpath) as bview:
        functions = [f for f in bview.functions if f.name.lower() == sym_name]
        function = functions[0]

        print('```mermaid')
        print(func_to_mermaid(function))
        print('```') 



