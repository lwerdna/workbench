#!/usr/bin/env python
#
# command-line BinaryNinja lifter

import os
import sys
import binascii

import binaryninja
from binaryninja import binaryview

from unicorn import *
from unicorn.arm_const import *

def usage():
    print('usage: %s <platform> <bytes>' % sys.argv[0])
    print('       %s <path>' % sys.argv[0])
    print('       %s <path> <symname>' % sys.argv[0])
    print('')
    print('examples:')
    print('    %s linux-armv7 14 d0 4d e2 01 20 a0 e1 00 30 a0 e1 00 c0 a0 e3' % sys.argv[0])
    print('    %s ~/fdumps/filesamples/hello-linux-x64.elf' % sys.argv[0])
    print('    %s ~/fdumps/filesamples/hello-linux-x64.elf _start' % sys.argv[0])
    print('')
    print('platforms: ' + ', '.join(map(str, list(binaryninja.Platform))))
    sys.exit(-1)

if __name__ == '__main__':
    bview = None

    if len(sys.argv)==1:
        usage()

    plat_name = sys.argv[1]
    byte_list = sys.argv[2:]
    data = bytes.fromhex(''.join(byte_list))
    plat = binaryninja.Platform[plat_name]
    bview = binaryview.BinaryView.new(data)
    bview.platform = plat
    bview.add_function(0, plat=plat)
    functions = list(bview.functions)
    bview.update_analysis_and_wait()

    if bview.arch.name == 'armv7':
        from emulate_aarch32 import *
        uc = spawn_vm()

    show_context(uc)

#    for func in functions:
#        for block in func.low_level_il:
#            for insn in block:
#                emulate_instruction(insn)

