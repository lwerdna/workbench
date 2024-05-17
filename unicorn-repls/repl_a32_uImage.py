#!/usr/bin/env python

# repl an A32 uImage (uBoot headered image/zImage)

import sys
import struct

from unicorn import *
from unicorn.arm_const import *

import aarch32
from helpers import *

if __name__ == '__main__':
    fpath = sys.argv[1]
    blob = open(fpath, 'rb').read()

    # read uboot header
    # https://github.com/u-boot/u-boot/blob/master/include/image.h
    magic, _, _, size, load, ep, _, os, arch, type_, _ = struct.unpack_from('>IIIIIIIBBBB', blob)
    assert magic == 0x27051956
    assert os == 5 # IH_OS_LINUX
    assert arch == 2 # IH_ARCH_ARM
    assert type_ == 2 # IH_TYPE_KERNEL

    print(f'len(blob) == 0x{len(blob):X}')
    print(f'     size == 0x{size:X}')
    print(f'     load == 0x{load:X}')

    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

    # create memory
    map_needed_pages(uc, load, size, UC_PROT_ALL)

    # write uImage (discluding header)
    uc.mem_write(load, blob[64:64+size])
    print('wrote %02X %02X %02X %02X to 0x%08X\n' % (blob[64], blob[65], blob[66], blob[67], load))

    print(get_hex_dump(uc.mem_read(load, 0x40), load))

    #
    uc.reg_write(UC_ARM_REG_R0, 0)
    uc.reg_write(UC_ARM_REG_R1, 0x0) # machine type number
    uc.reg_write(UC_ARM_REG_R2, 0x0) # atags or device tree
    uc.reg_write(UC_ARM_REG_PC, ep)

    print(f'starting emulation @0x{ep:X}')

    aarch32.repl(uc)
