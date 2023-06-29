#!/usr/bin/env python

import struct

from unicorn import *
from unicorn.x86_const import *

from md5_x64_dump import *

def align_down(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up(addr):
    return align_down(addr) + 0x1000 if (addr & 0xFFF) else addr

def push_qword(uc, value):
    addr = uc.reg_read(UC_X86_REG_RSP) - 8
    uc.reg_write(UC_X86_REG_RSP, addr)
    uc.mem_write(addr, struct.pack('<Q', value))

def alloc_stack(uc, amount):
    addr = uc.reg_read(UC_X86_REG_RSP) - amount
    uc.reg_write(UC_X86_REG_RSP, addr)
    return addr

def free_stack(uc, amount):
    uc.reg_write(UC_X86_REG_RSP, uc.reg_read(UC_X86_REG_RSP) + amount)

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

def setup_machine():
    uc = Uc(UC_ARCH_X86, UC_MODE_64)

    # calculate code area
    seg_start = align_down(min(f['address'] for f in functions))
    seg_end = align_up(max(f['address'] + f['length'] for f in functions))
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

name2addr = {f['name']: f['address'] for f in functions}

uc = setup_machine()
uc.mem_map(0, 4096) # so we can return to 0
uc.mem_map(0x100008000, 0x100009000) # for _PADDING and other __data crap

# create the md5 context
p_context = alloc_stack(uc, 128)
print(f'MD5_CTX allocated to 0x{p_context:X}')

print('calling MD5Init(&context)')
uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
push_qword(uc, 0) # return address
uc.emu_start(name2addr['_MD5Init'], 0)

print('calling MD5Update(&context, "The quick brown fox jumps over the lazy dog", 43)')
uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
buf = alloc_stack(uc, 64)
uc.mem_write(buf, b'The quick brown fox jumps over the lazy dog')
uc.reg_write(UC_X86_REG_RSI, buf) # RSI = arg1
uc.reg_write(UC_X86_REG_RDX, 43) # RDX = arg2
push_qword(uc, 0) # return address
uc.emu_start(name2addr['_MD5Update'], 0)
free_stack(uc, 64)

data = uc.mem_read(p_context, 128)
print(hexdump(data, p_context))

print('calling MD5Final(digest, &context)')
p_digest = alloc_stack(uc, 16)
uc.reg_write(UC_X86_REG_RDI, p_digest) # RDI = arg0
uc.reg_write(UC_X86_REG_RSI, p_context) # RSI = arg1
push_qword(uc, 0) # return address
print(f'p_context: 0x{p_context:X}')
print(f'p_digest: 0x{p_digest:X}')

def callback_code(mu, address, size, user_data):
    rax = uc.reg_read(UC_X86_REG_RAX)
    rcx = uc.reg_read(UC_X86_REG_RCX)
    rdx = uc.reg_read(UC_X86_REG_RDX)
    rdi = uc.reg_read(UC_X86_REG_RDI)
    rsi = uc.reg_read(UC_X86_REG_RSI)
    rip = uc.reg_read(UC_X86_REG_RIP)
    print(f'rip=0x{rip:X} rax=0x{rax:X} rcx=0x{rcx:X} rdx=0x{rdx:X} rdi=0x{rdi:X} rsi=0x{rsi:X}')
#uc.hook_add(UC_HOOK_CODE, callback_code)

uc.emu_start(name2addr['_MD5Final'], 0)

data = uc.mem_read(p_digest, 256)
print(hexdump(data, p_digest))

