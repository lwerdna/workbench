#!/usr/bin/env python
#
# disable LC_FUNCTION_STARTS in Mach-O executable

import os, sys, re, pprint
from struct import pack, unpack

with open(sys.argv[1], 'rb+') as fp:
    magic = unpack('<I', fp.read(4))[0]
    assert magic == 0xFEEDFACF # MH_MAGIC_64
    cputype = unpack('<I', fp.read(4))[0]
    assert cputype == (0x1000000 | 7) # CPU_ARCH_ABI64 | CPU_TYPE_X86
    (_, _, cmds_n, _, _, _) = unpack('<IIIIII', fp.read(6*4)) # remainder of mach_header_64

    #print('cmds_n: %d' % cmds_n)
    for i in range(cmds_n):
        (cmd_id, cmd_size) = unpack('<II', fp.read(8))
        #print('command %d / %d is 0x%X with size %d' % (i+1, cmds_n, cmd_id, cmd_size))
        if cmd_id == 0x26: # LC_FUNCTION_STARTS
            print('found LC_FUNCTION_STARTS load command, zeroing data offset, data length')
            fp.write(b'\x00\x00\x00\x00\x00\x00\x00\x00')
            break
        fp.seek(cmd_size - 8, 1)


