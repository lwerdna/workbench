#!/usr/bin/env python

import os, sys

from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine

# block: miasm.core.asmblock.AsmBlock
def block_id(block):
    return f'block_{block.loc_key.key}'

# block: miasm.core.asmblock.AsmBlock
def block_label(block):
    result = []
    for line in block.lines:
        result.append('%X: %s' % (line.offset, str(line)))
    return '<br>'.join(result)

# cfg: miasm.core.asmblock.AsmCFG
def cfg_to_mermaid(cfg):
    result = ['graph']

    # block identifiers and labels
    for block in list(cfg.blocks):
        label = block_label(block).replace('"', '&quot;')
        result.append('\t%s["%s"]' % (block_id(block), label))

    # block identifier to block identifier
    for (loc_src, loc_dst) in cfg.edges():
        block_src = cfg.loc_key_to_block(loc_src)
        block_dst = cfg.loc_key_to_block(loc_dst)
        result.append('\t%s --> %s' % (block_id(block_src), block_id(block_dst)))

    return '\n'.join(result)

def resolve_symbol(container, sym_name):
    loc_key = container.loc_db.get_name_location(sym_name)
    return container.loc_db.get_location_offset(loc_key)

if __name__ == '__main__':
    fpath = '../testbins/tests-linux-x64-elf'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    sym_name = 'collatz_message'
    if sys.argv[2:]:
        sym_name = sys.argv[2]

    with open(fpath, 'rb') as fp:
        data = fp.read()

    # Container is superclass of ContainerELF, ContainerPE, etc.
    # Is container the analog of Binja's BinaryView?
    #
    # container.arch = 'x86_64'
    container = Container.from_string(data)

    # list all symbols / addresses available from the container
    ldb = container.loc_db
    for k in ldb.loc_keys:
        offset = ldb.get_location_offset(k)
        names = [x.decode() for x in ldb.get_location_names(k)]

        #print('%08X:' % offset)
        #for name in names:
        #    print('\t"%s"' % name)

    # disassemble the given symbol
    machine = Machine(container.arch)
    disassembler = machine.dis_engine(container.bin_stream, loc_db=container.loc_db)

    sym_offs = resolve_symbol(container, sym_name)
    #print('%s is located at: 0x%X' % (sym_name, sym_offs))

    # miasm.core.asmblock.AsmCFG
    cfg = disassembler.dis_multiblock(offset=sym_offs)

    print('```mermaid')
    print(cfg_to_mermaid(cfg))
    print('```')
