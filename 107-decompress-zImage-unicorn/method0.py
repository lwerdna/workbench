#!/usr/bin/env python

import re
import sys
import time
import struct

from unicorn import *
from unicorn.arm_const import *

#------------------------------------------------------------------------------
# VM setup
#------------------------------------------------------------------------------

def align_down_4k(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up_4k(addr):
    return align_down_4k(addr) + 0x1000 if (addr & 0xFFF) else addr

def align_4k(addr):
    return (align_down_4k(addr), align_up_4k(addr+1))

#------------------------------------------------------------------------------
# TRACKING
#------------------------------------------------------------------------------

def extent(uc, addr):
    regions = list(uc.mem_regions())
    regions = [(a, b+1, c) for (a, b, c) in regions] # convert [a,b] -> [a,b)
    regions = sorted(regions, key=lambda r: r[0])

    # search for region that contains addr
    for i, (lo, hi, prot) in enumerate(regions):
        if lo <= addr < hi:
            break
    else:
        assert False, f'seeking extent of address 0x{addr:X} that isnt mapped'

    for (a, b, p) in regions[i+1:]:
        if a == hi and prot == p:
            hi = b
        else:
            break

    for (a, b, p) in reversed(regions[0:i]):
        if b == lo and prot == p:
            lo = a
        else:
            break

    print(f'0x{addr:X} was contained in [0x{lo:X}, 0x{hi:X}')
    return lo, hi

#------------------------------------------------------------------------------
# VM setup
#------------------------------------------------------------------------------

def map_mem_helper(uc, addr, size, perms=None):

    if perms is None:
        perms = UC_PROT_READ|UC_PROT_WRITE

    lo = align_down_4k(addr)
    hi = align_up_4k(addr+size)

    permstr = ''
    permstr += 'R' if perms & UC_PROT_READ else '-'
    permstr += 'W' if perms & UC_PROT_WRITE else '-'
    permstr += 'X' if perms & UC_PROT_EXEC else '-'

    print(f'map [0x{lo:X}, 0x{hi:X}) {permstr}')
    uc.mem_map(lo, hi-lo, perms)

def hook_mem_fetch_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED FETCH FROM ADDRESS: 0x{address:X})')
    return False

def hook_mem_write_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    #extra = f' ("{chr(value)}")' if size==1 else ''
    #print(f'{pc:08X} UNMAPPED WRITE: {size} bytes {hex(value)} to 0x{address:X}{extra}')
    map_mem_helper(uc, address, 1)
    return True

def hook_mem_read_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED READ: {size} bytes from 0x{address:X}')
    map_mem_helper(uc, address, 1)
    return True

def hook_mem_fetch_prot(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} EXEC FROM NX MEM AT 0x{address:X}')

    #print(f'protecting [{lo:08X}, {hi:08X})')
    #uc.mem_protect(lo, hi-lo-0x1000, perms=UC_PROT_READ|UC_PROT_WRITE|UC_PROT_EXEC)

    #breakpoint()
    regions = list(uc.mem_regions())
    regions = [(a, b+1, c) for (a, b, c) in regions] # convert [a,b] -> [a,b)
    regions = sorted(regions, key=lambda r: r[0])

    # get the extent of this region
    lo, hi = extent(uc, address)
    print(f'extent: [{lo:08X}, {hi:08X})')

    # does the remainder of the current page exist in the first page of the largest region?
    # (is it likely we're a relocated version of the zImage?)
    largest = regions[0]
    for region in regions:
        if region[1]-region[0] > largest[1]-largest[0]:
            largest = region

    remainder = uc.mem_read(address, align_up_4k(address+1) - address)
    if not (largest[0] <= address < largest[1]) and uc.mem_read(largest[0], 0x1000).find(remainder) != -1:
        print('detected relocated kernel')

        print('flipping protections')
        for a, b, prot in uc.mem_regions():
            # +X the region we jumped to
            if lo <= a < hi:
                uc.mem_protect(a, b-a+1, UC_PROT_READ|UC_PROT_WRITE|UC_PROT_EXEC)
            # -X other regions
            else:
                uc.mem_protect(a, b-a+1, UC_PROT_READ|UC_PROT_WRITE)

        print('continuing')
    else:
        blob = uc.mem_read(lo, hi-lo)
        fpath = 'dump.bin'
        print(f'writing 0x{len(blob):X} ({len(blob)}) bytes to {fpath}')
        with open(fpath, 'wb') as fp:
            fp.write(blob)
        print('stopping emulation')
        uc.emu_stop()
        print('STOPPED')

    return True

def setup_machine():
    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

    # hook unmapped fetches
    uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, hook_mem_fetch_unmapped)
    # hook unmapped writes
    uc.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, hook_mem_write_unmapped)
    # hook unmapped reads
    uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED, hook_mem_read_unmapped)
    # hook execute from nx memory
    uc.hook_add(UC_HOOK_MEM_FETCH_PROT, hook_mem_fetch_prot)

    return uc

if __name__ == '__main__':
    fpath = sys.argv[1]
    blob = open(fpath, 'rb').read()

    # read uboot header
    # https://github.com/u-boot/u-boot/blob/master/include/image.h
    magic, _, _, size, load, ep, _, os, arch, type_, compression = struct.unpack_from('>IIIIIIIBBBB', blob)
    assert magic == 0x27051956
    assert os == 5 # IH_OS_LINUX
    assert arch == 2 # IH_ARCH_ARM
    assert type_ == 2 # IH_TYPE_KERNEL

    #if compression == 0:
    #    print('no compression! emulation not required!')
    #    sys.exit(0)

    print(f'len(blob) == 0x{len(blob):X}')
    print(f'     size == 0x{size:X}')

    uc = setup_machine()
    map_mem_helper(uc, load, size, UC_PROT_READ|UC_PROT_WRITE|UC_PROT_EXEC)

    # write uImage (discluding header)
    uc.mem_write(load, blob[64:64+size])

    #
    uc.reg_write(UC_ARM_REG_R0, 0)
    uc.reg_write(UC_ARM_REG_R1, 0x0) # machine type number
    uc.reg_write(UC_ARM_REG_R2, 0x0) # atags or device tree
    uc.reg_write(UC_ARM_REG_PC, ep)

    print(f'starting emulation @0x{load:X}')
    uc.emu_start(load, 0)

