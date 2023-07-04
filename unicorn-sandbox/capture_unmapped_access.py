#!/usr/bin/env python

import os
import sys

import struct

from keystone import *

from unicorn import *
from unicorn.x86_const import *

from helpers import *

ks = None
def assemble_single(text):
    global ks
    if not ks:
        ks = Ks(KS_ARCH_X86, KS_MODE_64)

    # encoding is a list of integers [0,256)
    encoding, count = ks.asm(text)
    return bytes(encoding)

def setup_machine():
    uc = Uc(UC_ARCH_X86, UC_MODE_64)

    code = b''
    code += assemble_single('mov rax, 0xAAAA0000')
    code += assemble_single('mov rax, [rax]') # invalid read
    code += assemble_single('nop')
    code += assemble_single('nop')
    code += assemble_single('mov rbx, 0xBBBB0000')
    code += assemble_single('mov [rbx], rax') # invalid write
    code += 256 * assemble_single('nop')

    # calculate code area
    seg_start = 0
    seg_end = align_up_4k(len(code))
    print(f'creating code segment [0x{seg_start:X}, 0x{seg_end:X})')

    # create code area
    uc.mem_map(seg_start, seg_end-seg_start)
    uc.mem_write(0, code)

    return uc

# in this callback, we map in memory as needed
def callback_jit_mapping(uc, access, addr, size, value, context):
    if access == UC_MEM_READ_UNMAPPED:
        descr = 'read from'
    elif access == UC_MEM_WRITE_UNMAPPED:
        descr = 'write to'
    else:
        breakpoint()

    print(f'unmapped {size}-byte {descr} 0x{addr:X}')
    seg_start = align_down_4k(addr)
    seg_end = align_up_4k(addr + 8)
    print(f'mapping in [0x{seg_start:X}, 0x{seg_end:X})')
    uc.mem_map(seg_start, seg_end-seg_start)
    uc.mem_write(addr, b'\xef\xbe\xad\xde\x00\x00\x00\x00')

    # if True, unicorn will try again (assuming you fixed the execution environment)
    # if False, it will continue throwing unicorn.unicorn.UcError: Invalid memory read (UC_ERR_READ_UNMAPPED)
    return True

if __name__ == '__main__':
    setup_machine()
    uc = setup_machine()

    # grep 'UC_HOOK_' in unicorn_const.py for others
    uc.hook_add(UC_HOOK_MEM_UNMAPPED, callback_jit_mapping)

    uc.emu_start(0, 0x100)

    rip = uc.reg_read(UC_X86_REG_RIP)
    rax = uc.reg_read(UC_X86_REG_RAX)
    print(f'rip={rip:016X} rax={rax:016X}')

