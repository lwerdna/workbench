#!/usr/bin/env python

import os
import sys
import struct

from unicorn import *
from unicorn.arm_const import *

from md5_armv7_dump import *

from helpers import *

def setup_machine():
    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

    # calculate code area
    seg_start = align_down_4k(min(f['address'] for f in functions))
    seg_end = align_up_4k(max(f['address'] + f['length'] for f in functions))
    print(f'creating code segment [0x{seg_start:X}, 0x{seg_end:X})')

    # create code area
    uc.mem_map(seg_start, seg_end-seg_start)
    for function in functions:
        print(f'writing 0x{function["length"]:X} bytes of {function["name"]} to 0x{function["address"]:X}')
        uc.mem_write(function["address"], b''.join(function['instructions']))

    # create stack area
    STACK_MEM_START  = 0xF0000000
    STACK_MEM_LENGTH = 2**16    
    print(f'creating stack segment [0x{STACK_MEM_START:X}, 0x{STACK_MEM_START+STACK_MEM_LENGTH:X})')
    uc.mem_map(STACK_MEM_START, STACK_MEM_LENGTH)
    uc.reg_write(UC_ARM_REG_SP, STACK_MEM_START + STACK_MEM_LENGTH - 8*32) # 32 pushes

    return uc

if __name__ == '__main__':
    name2addr = {f['name']: f['address'] for f in functions}

    uc = setup_machine()

    # static unsigned char PADDING[64] = {0x80, 0, 0, ..., 0}
    uc.mem_map(0x6000, 0x7000) # for _PADDING
    uc.mem_write(0x6000, b'\x80')

    # create the md5 context
    p_context = arm_alloc_stack(uc, 128)
    print(f'MD5_CTX allocated to 0x{p_context:X}')

    print('calling MD5Init(&context)')
    uc.reg_write(UC_ARM_REG_R0, p_context) # R0 = arg0
    arm_push_dword(uc, 0) # return address
    uc.emu_start(name2addr['MD5Init'], 0)

    data = uc.mem_read(p_context, 128)
    print(hexdump(data, p_context))

    print('calling MD5Update(&context, "The quick brown fox jumps over the lazy dog", 43)')
    uc.reg_write(UC_ARM_REG_R0, p_context) # R0 = arg0
    buf = arm_alloc_stack(uc, 64)
    uc.mem_write(buf, b'The quick brown fox jumps over the lazy dog')
    uc.reg_write(UC_ARM_REG_R1, buf) # R1 = arg1
    uc.reg_write(UC_ARM_REG_R2, 43) # R2 = arg2
    arm_push_dword(uc, 0) # return address
    uc.emu_start(name2addr['MD5Update'], 0)
    arm_free_stack(uc, 64)

    data = uc.mem_read(p_context, 128)
    print(hexdump(data, p_context))

    print('calling MD5Final(digest, &context)')
    p_digest = arm_alloc_stack(uc, 16)
    uc.reg_write(UC_ARM_REG_R0, p_digest) # R0 = arg0
    uc.reg_write(UC_ARM_REG_R1, p_context) # R1 = arg1
    arm_push_dword(uc, 0) # return address
    print(f'p_context: 0x{p_context:X}')
    print(f'p_digest: 0x{p_digest:X}')

    def callback_code(mu, address, size, user_data):
        r0 = uc.reg_read(UC_ARM_REG_R0)
        r1 = uc.reg_read(UC_ARM_REG_R1)
        r2 = uc.reg_read(UC_ARM_REG_R2)
        r3 = uc.reg_read(UC_ARM_REG_R3)
        sp = uc.reg_read(UC_ARM_REG_SP)
        pc = uc.reg_read(UC_ARM_REG_PC)
        #print(f'{pc:08X}: r0=0x{r0:X} r1=0x{r1:X} r2=0x{r2:X} r3=0x{r3:X} sp=0x{sp:X}')

        if pc == 0xff0:
            print('AFTER PADDING!')
            print(hexdump(uc, r1))

    uc.hook_add(UC_HOOK_CODE, callback_code)

    uc.emu_start(name2addr['MD5Final'], 0)

    print('result: (expect: 9e107d9d372bb6826bd81d3542a419d6)')
    data = uc.mem_read(p_digest, 16)
    print(hexdump(data, p_digest))
