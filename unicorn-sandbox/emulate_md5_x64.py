#!/usr/bin/env python

import struct

from unicorn import *
from unicorn.x86_const import *

from md5_x64_dump import *

from helpers import *

def setup_machine():
    uc = Uc(UC_ARCH_X86, UC_MODE_64)

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
    uc.reg_write(UC_X86_REG_RSP, STACK_MEM_START + STACK_MEM_LENGTH - 8*32) # 32 pushes

    return uc

if __name__ == '__main__':
    name2addr = {f['name']: f['address'] for f in functions}

    uc = setup_machine()
    uc.mem_map(0, 4096) # so we can return to 0

    # static unsigned char PADDING[64] = {0x80, 0, 0, ..., 0}
    uc.mem_map(0x100008000, 0x100009000) # for _PADDING
    uc.mem_write(0x100008050, b'\x80')

    # create the md5 context
    p_context = x64_alloc_stack(uc, 128)
    print(f'MD5_CTX allocated to 0x{p_context:X}')

    print('calling MD5Init(&context)')
    uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
    x64_push_qword(uc, 0) # return address
    uc.emu_start(name2addr['_MD5Init'], 0)

    print('calling MD5Update(&context, "The quick brown fox jumps over the lazy dog", 43)')
    uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
    buf = x64_alloc_stack(uc, 64)
    uc.mem_write(buf, b'The quick brown fox jumps over the lazy dog')
    uc.reg_write(UC_X86_REG_RSI, buf) # RSI = arg1
    uc.reg_write(UC_X86_REG_RDX, 43) # RDX = arg2
    x64_push_qword(uc, 0) # return address
    uc.emu_start(name2addr['_MD5Update'], 0)
    x64_free_stack(uc, 64)

    #data = uc.mem_read(p_context, 128)
    #print(hexdump(data, p_context))

    print('calling MD5Final(digest, &context)')
    p_digest = x64_alloc_stack(uc, 16)
    uc.reg_write(UC_X86_REG_RDI, p_digest) # RDI = arg0
    uc.reg_write(UC_X86_REG_RSI, p_context) # RSI = arg1
    x64_push_qword(uc, 0) # return address
    print(f'p_context: 0x{p_context:X}')
    print(f'p_digest: 0x{p_digest:X}')

    #def callback_code(mu, address, size, user_data):
    #    rax = uc.reg_read(UC_X86_REG_RAX)
    #    rcx = uc.reg_read(UC_X86_REG_RCX)
    #    rdx = uc.reg_read(UC_X86_REG_RDX)
    #    rdi = uc.reg_read(UC_X86_REG_RDI)
    #    rsi = uc.reg_read(UC_X86_REG_RSI)
    #    rip = uc.reg_read(UC_X86_REG_RIP)
    #    print(f'rip=0x{rip:X} rax=0x{rax:X} rcx=0x{rcx:X} rdx=0x{rdx:X} rdi=0x{rdi:X} rsi=0x{rsi:X}')
    #uc.hook_add(UC_HOOK_CODE, callback_code)

    uc.emu_start(name2addr['_MD5Final'], 0)

    print('result: (expect: 9e107d9d372bb6826bd81d3542a419d6)')
    data = uc.mem_read(p_digest, 16)
    print(hexdump(data, p_digest))
