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

# https://gist.github.com/mzpqnxow/a368c6cd9fae97b87ef25f475112c84c
def hexdump(src, addr=0, length=16, sep='.'):
    FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or sep for x in range(256)])
    lines = []
    for c in range(0, len(src), length):
        chars = src[c: c + length]
        hex_ = ' '.join(['{:02x}'.format(x) for x in chars])
        if len(hex_) > 24:
            hex_ = '{}{}'.format(hex_[:24], hex_[24:])
        printable = ''.join(['{}'.format((x <= 127 and FILTER[x]) or sep) for x in chars])
        lines.append('{0:08x}: {1:{2}s} {3:{4}s}'.format(addr+c, hex_, length * 3, printable, length))
    return '\n'.join(lines)

#------------------------------------------------------------------------------
# VM setup
#------------------------------------------------------------------------------

def map_mem_helper(uc, addr, size, perms=UC_PROT_READ|UC_PROT_WRITE|UC_PROT_ALL):
    global regions
    if regions.overlaps(addr):
        return

    lo = align_down_4k(addr)
    hi = align_up_4k(addr+size)

    print(f'uc.mem_map(0x{lo:X}, 0x{hi-lo:X}) -> [0x{lo:X}, 0x{hi:X})')
    # make it not executable, to capture when jump occurs
    uc.mem_map(lo, hi-lo, perms=perms)

    # update regions
    regions[lo:hi] = True
    regions.merge_overlaps(strict=False)

    # print regions
    print('current regions: ')
    for region in sorted(regions, key=lambda r: r.begin):
        print(f'[{region.begin:08X}, {region.end:08X})')

def hook_mem_fetch_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED FETCH FROM ADDRESS: 0x{address:X})')
    return False

def hook_mem_write_unmapped(uc, access, address, size, value, user_data):

    pc = uc.reg_read(UC_ARM_REG_PC)
    extra = f' ("{chr(value)}")' if size==1 else ''
    print(f'{pc:08X} UNMAPPED WRITE: {size} bytes {hex(value)} to 0x{address:X}{extra}')
    map_mem_helper(uc, address, 1)
    return True

def hook_mem_read_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED READ: {size} bytes from 0x{address:X})')
    map_mem_helper(uc, address, 1)
    return True

def hook_mem_fetch_prot(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} EXEC FROM NX MEM AT 0x{address:X}')

    if 0:
        uc.emu_stop()
    else:
        map_mem_helper(uc, address, 1, UC_PROT_ALL)
        
    return True

def setup_machine():
    STACK_MEM_START = 0xC0000000
    STACK_MEM_LENGTH = 16 * 1024 * 1024 # 16mb

    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

    # set up stack
    #uc.mem_map(STACK_MEM_START, STACK_MEM_START+STACK_MEM_LENGTH)
    #uc.reg_write(UC_ARM_REG_SP, STACK_MEM_START + STACK_MEM_LENGTH)

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
    map_mem_helper(uc, load, size, UC_PROT_ALL)

    # write uImage (discluding header)
    uc.mem_write(load, blob[64:64+size])

    # 
    uc.reg_write(UC_ARM_REG_R0, 0)
    uc.reg_write(UC_ARM_REG_R1, 0x0) # machine type number
    uc.reg_write(UC_ARM_REG_R2, 0x0) # atags or device tree
    uc.reg_write(UC_ARM_REG_PC, ep)
   
    print(f'starting emulation @0x{load:X}')
    uc.emu_start(load, 0)

    # dump any regions that are not the original region
    regions.merge_overlaps(strict=False)

    for region in regions:
        if region.begin <= load < region.end:
            pass
        length = region.end - region.begin
        fname = f'{region.begin:08X}.bin'
        print(f'dumping 0x{length} ({length}) bytes to {fname}')
        with open(fname, 'wb') as fp:
            fp.write(uc.mem_read(region.begin, length))
