#!/usr/bin/env python

# Capture unmapped execution (fetch) from memory and automatically
# proceed. Requires the fetching instruction be appeased.

# Your UC_HOOK_MEM_FETCH_UNMAPPED callback will execute, and you can repair the
# context by setting RIP. But the original fetch still wants to execute, and
# without memory there, a UC_ERR_MAP error will happen, but your
# UC_HOOK_MEM_UNMAPPED callback will *NOT* execute.
#
# You must map in memory so the original fetch succeeds.
#
# I have found a citation!
# https://github.com/unicorn-engine/unicorn/blob/master/include/unicorn/unicorn.h
# > In the event of a UC_MEM_FETCH_UNMAPPED callback, the memory can be
# > mapped in as executable, in which case execution will resume from the fetched
# > address. The instruction pointer may be written to in order to change where
# > execution resumes, but the fetch must succeed if execution is to resume.

import os
import sys

import struct

from keystone import *

from unicorn import *
from unicorn.x86_const import *

def align_down_4k(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up_4k(addr):
    return align_down_4k(addr) + 0x1000 if (addr & 0xFFF) else addr

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
    code += assemble_single('call rax')
    print(f'nops start at 0x{len(code):X}')
    code += assemble_single('nop') * 32
    code += assemble_single('mov rbx, 0xBBBB0000')
    code += assemble_single('call rbx')
    print(f'nops start at 0x{len(code):X}')
    code += assemble_single('nop') * 32

    while len(code) < 0x1000:
        code += assemble_single('nop')

    # calculate code area
    seg_start = 0
    seg_end = align_up_4k(len(code))
    print(f'creating code segment [0x{seg_start:X}, 0x{seg_end:X})')

    # create code area
    uc.mem_map(seg_start, seg_end-seg_start)
    uc.mem_write(0, code)

    # create stack area
    uc.mem_map(0xF0000000, 0x1000);
    uc.reg_write(UC_X86_REG_RSP, 0xF0000000 + 0x1000);

    return uc

def callback_fetch(uc, access, addr, size, value, context):
    print(f'callback_fetch(addr=0x{addr:X})')
    assert access == UC_MEM_FETCH_UNMAPPED

    seg_start = align_down_4k(addr)
    seg_end = align_up_4k(addr+1)
    # REQUIRED!
    print(f'mapping in [0x{seg_start:X}, 0x{seg_end:X})')
    uc.mem_map(seg_start, seg_end-seg_start)

    # pop return address
    caller = struct.unpack('<Q', uc.mem_read(uc.reg_read(UC_X86_REG_RSP), 8))[0]
    uc.reg_write(UC_X86_REG_RSP, uc.reg_read(UC_X86_REG_RSP)+8)
    uc.reg_write(UC_X86_REG_RIP, caller)

    return True

def callback_unmapped(uc, access, addr, size, value, context):
    print(f'callback_unmapped(addr=0x{addr:X})')
    if access == UC_MEM_READ_UNMAPPED:
        descr = '*READ* from'
    elif access == UC_MEM_WRITE_UNMAPPED:
        descr = '*WRITE* to'
    else:
        breakpoint()

    return True

if __name__ == '__main__':
    uc = setup_machine()

    # grep 'UC_HOOK_' in unicorn_const.py for others
    uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, callback_fetch)
    uc.hook_add(UC_HOOK_MEM_UNMAPPED, callback_unmapped)

    uc.emu_start(0, 0x1000)

    rip = uc.reg_read(UC_X86_REG_RIP)
    rax = uc.reg_read(UC_X86_REG_RAX)
    print(f'rip={rip:016X} rax={rax:016X}')

