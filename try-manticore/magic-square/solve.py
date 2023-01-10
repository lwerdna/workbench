#!/usr/bin/env python

from manticore.native import Manticore
from manticore.core.state import TerminateState

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

def concrete_mem(state, addr, length):
    data = b''
    sym_mem = state.mem.read(addr, length)
    for i in range(length):
        value = state.concretize(sym_mem[i], 'ONE')
        assert type(value)==tuple and len(value)==1
        value = value[0]
        if type(value) == int:
            value = value.to_bytes(1, 'big')
        elif type(value) == bytes:
            pass
        else:
            breakpoint()
        data += value
    return data

def print_mem(state, addr, length):
    data = concrete_mem(state, addr, 32)
    print(hexdump(data, addr))

m = Manticore('./puzzle')

buf_addr = 0
@m.hook(0x2011a0)
def hookA(state):
    global buf_addr
    buf_addr = state.cpu.RDI
    print(f'{hex(state.cpu.RIP)}:')

@m.hook(0x20171F)
def hookE(state):
    global buf_addr
    print(f'{hex(state.cpu.RIP)}:')
    print_mem(state, buf_addr, 9)
    raise TerminateState('success')

m.run()
