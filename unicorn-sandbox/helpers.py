import struct

from unicorn import *
from unicorn.x86_const import *

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

def align_down_4k(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up_4k(addr):
    return align_down_4k(addr) + 0x1000 if (addr & 0xFFF) else addr

#------------------------------------------------------------------------------
# x64 helpers
#------------------------------------------------------------------------------
def x64_push_qword(uc, value):
    addr = uc.reg_read(UC_X86_REG_RSP) - 8
    uc.reg_write(UC_X86_REG_RSP, addr)
    uc.mem_write(addr, struct.pack('<Q', value))

def x64_alloc_stack(uc, amount):
    addr = uc.reg_read(UC_X86_REG_RSP) - amount
    uc.reg_write(UC_X86_REG_RSP, addr)
    return addr

def x64_free_stack(uc, amount):
    uc.reg_write(UC_X86_REG_RSP, uc.reg_read(UC_X86_REG_RSP) + amount)
