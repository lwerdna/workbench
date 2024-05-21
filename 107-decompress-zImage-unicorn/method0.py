#!/usr/bin/env python

import re
import sys
import struct

from intervaltree import IntervalTree

from unicorn import *
from unicorn.arm_const import *

regions = IntervalTree()

#------------------------------------------------------------------------------
# VM setup
#------------------------------------------------------------------------------

def align_down_4k(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up_4k(addr):
    return align_down_4k(addr) + 0x1000 if (addr & 0xFFF) else addr

def align_4k(addr):
    return (align_down_4k(addr), align_up_4k(addr+1))

def alloc_stack(uc, length):
    sp = uc.reg_read(UC_ARM_REG_SP)
    uc.reg_write(UC_ARM_REG_SP, sp-length)
    return sp-length

def data2hex(data):
    return ' '.join(f'{x:02X}' for x in data)

#------------------------------------------------------------------------------
# TRACKING
#------------------------------------------------------------------------------
regions = set()
regions_x = set()
candidate = set()

def enveloping(addr):
    global regions

    # sort regions by start address
    tmp = sorted(regions, key=lambda reg: reg[0])

    # find region
    for i, (lo, hi) in enumerate(tmp):
        if lo <= addr < hi:
            break
    else:
        raise Exception()

    # find how long it continues
    lo, hi = tmp[i]
    for (a, b) in tmp[i+1:]:
        if a == hi:
            hi = b
        else:
            break

    return (lo, hi)

#------------------------------------------------------------------------------
# VM setup
#------------------------------------------------------------------------------

def map_mem_helper(uc, addr, size, perms=None):
    global regions

    if perms is None:
        perms = UC_PROT_READ|UC_PROT_WRITE

    lo = align_down_4k(addr)
    hi = align_up_4k(addr+size)
    regions.add((lo, hi))

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
    print(f'{pc:08X} UNMAPPED READ: {size} bytes from 0x{address:X})')
    map_mem_helper(uc, address, 1)
    return True

def hook_mem_fetch_prot(uc, access, address, size, value, user_data):
    global regions

    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} EXEC FROM NX MEM AT 0x{address:X}')

    lo, hi = enveloping(address)
    print(f'enveloping addresses [{lo:08X},{hi:08X})')

    print(f'protecting [{lo:08X}, {hi:08X})')
    uc.mem_protect(lo, hi-lo-0x1000, perms=UC_PROT_READ|UC_PROT_WRITE|UC_PROT_EXEC)

    # unmap every address
    regions_new = set()
    for a, b in sorted(regions, key=lambda reg: reg[0]):
        if lo <= a <= hi:
            #print(f'protecting [{a:08X}, {b:08X})')
            #uc.mem_protect(a, b-a, perms=UC_PROT_READ|UC_PROT_WRITE|UC_PROT_EXEC)
            regions_new.add((a, b))
        else:
            print(f'unmapping [{a:08X}, {b:08X})')
            uc.mem_unmap(a, b-a)

    regions = regions_new
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
    magic, _, _, size, load, ep, _, os, arch, type_, _ = struct.unpack_from('>IIIIIIIBBBB', blob)
    assert magic == 0x27051956
    assert os == 5 # IH_OS_LINUX
    assert arch == 2 # IH_ARCH_ARM
    assert type_ == 2 # IH_TYPE_KERNEL

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

