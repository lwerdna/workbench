#!/usr/bin/env python

import os, sys, re, pprint

from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine

def resolve_symbol(container, sym_name):
    loc_key = container.loc_db.get_name_location(sym_name)
    return container.loc_db.get_location_offset(loc_key)

if __name__ == '__main__':
    fpath = '../testbins/tests-linux-x64-elf'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    sym_name = 'some_loops'
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

        print('%08X:' % offset)
        for name in names:
            print('\t"%s"' % name)

    # disassemble the given symbol
    machine = Machine(container.arch)
    disassembler = machine.dis_engine(container.bin_stream, loc_db=container.loc_db)

    sym_offs = resolve_symbol(container, sym_name)
    print('%s is located at: 0x%X' % (sym_name, sym_offs))
    disasm = disassembler.dis_multiblock(offset=sym_offs)
    print(disasm)

    open('/tmp/tmp.dot', 'w').write(disasm.dot())
    os.system('dot /tmp/tmp.dot -Tpng -o /tmp/tmp.png')
