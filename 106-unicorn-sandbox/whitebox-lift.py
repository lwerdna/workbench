#!/usr/bin/env python

# call an unknown/obfuscated/whitebox? crypto routine from a memory dump
# (serving mainly as an example for future similar tasks)
#
# - find further locations needing rip/lift by hooking UC_HOOK_MEM_FETCH_UNMAPPED
# - set up context, call function, extract results
# - execute only the intended function by setting LR=0 and emu_start(..., 0)

import re
import sys

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

def alloc_stack(uc, length):
    sp = uc.reg_read(UC_ARM_REG_SP)
    uc.reg_write(UC_ARM_REG_SP, sp-length)
    return sp-length

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

def handle_memcpy(uc, addr, size, user_data):
    dst = uc.reg_read(UC_ARM_REG_R0)
    src = uc.reg_read(UC_ARM_REG_R1)
    len = uc.reg_read(UC_ARM_REG_R2)
    lr = uc.reg_read(UC_ARM_REG_LR)
    print(f'memcpy(0x{dst:X}, 0x{src:X}, 0x{len:X}) return to 0x{lr:X}')
    uc.mem_write(dst, bytes(uc.mem_read(src, len)))
    uc.reg_write(UC_ARM_REG_PC, lr)
    return True

def handle_memset(uc, addr, size, user_data):
    dst = uc.reg_read(UC_ARM_REG_R0)
    char = uc.reg_read(UC_ARM_REG_R1) & 0xFF
    len = uc.reg_read(UC_ARM_REG_R2)
    lr = uc.reg_read(UC_ARM_REG_LR)
    print(f'memset(0x{dst:X}, 0x{char:X}, 0x{len:X}) return to 0x{lr:X}')
    uc.mem_write(dst, char.to_bytes(1, 'little') * size)
    uc.reg_write(UC_ARM_REG_PC, lr)
    return True

def hook_mem_fetch_unmapped(uc, access, address, size, value, user_data):
    print(f'hook_mem_fetch_unmapped(addr=0x{address:X})')
    is_mapped = any(start<=address<=end for (start,end,_) in uc.mem_regions())
    if not is_mapped:
        lo, hi = align_4k(address)
        print(f'uc.mem_map(0x{lo:X}, 0x{hi-lo:X})')
        uc.mem_map(lo, hi-lo)
        uc.mem_write(lo, b'\x00\xf0\x20\xe3'*1024) # fill with nop's
    uc.mem_write(address, b'\xfe\xff\xff\xea') # loop
    return True

def setup_machine():
    STACK_MEM_START = 0xC0000000
    STACK_MEM_LENGTH = 16 * 1024 * 1024 # 16mb

    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

    # set up stack
    uc.mem_map(STACK_MEM_START, STACK_MEM_START+STACK_MEM_LENGTH)
    uc.reg_write(UC_ARM_REG_SP, STACK_MEM_START + STACK_MEM_LENGTH)

    # read dumped images
    for fpath in ['34020000.bin']:
        m = re.match(r'^([a-hA-H0-9]+)\.bin$', fpath)
        addr = int(m.group(1), 16)
        data = open(fpath, 'rb').read()
        print(f'setting up [0x{addr:X}, 0x{addr+len(data):X}) from {fpath}')
        uc.mem_map(addr, len(data))
        uc.mem_write(addr, data)

    # hook fetches
    uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, hook_mem_fetch_unmapped)
    # hook memcpy
    uc.hook_add(UC_HOOK_CODE, handle_memcpy, begin=0x3501abcc, end=0x3501abcc)
    # hook memset
    uc.hook_add(UC_HOOK_CODE, handle_memset, begin=0x3521cde4, end=0x3521cde4)

    return uc

def decrypt(ctext):
    # set up emulator
    uc = setup_machine(uc)

    # arg0: ciphertext
    pctext = alloc_stack(uc, len(ctext))
    uc.mem_write(pctext, ctext)
    uc.reg_write(UC_ARM_REG_R0, pctext)
    # arg1: plaintext
    pptext = alloc_stack(uc, len(ctext))
    uc.reg_write(UC_ARM_REG_R1, pptext)
    # arg2: length
    uc.reg_write(UC_ARM_REG_R2, len(ctext))

    # call function
    uc.reg_write(UC_ARM_REG_LR, 0) # return to 0
    uc.emu_start(0x340266c8, 0); # emulate to 0
    return uc.mem_read(pptext, len(ctext))

if __name__ == '__main__':
    fpath = sys.argv[1]
    ctext = open(fpath, 'rb').read()
    ptext = decrypt(ctext)
    print(hexdump(ptext, 0))

