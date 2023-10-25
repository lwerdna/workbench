#!/usr/bin/env python

import os, sys

import binaryninja

def stringify(data):
    return "b'" + ''.join([f'\\x{byte:02X}' for byte in data]) + "'"

if __name__ == '__main__':
    fpath = sys.argv[1] if sys.argv[1:] else '../testbins/md5/md5_x64-macos'

    bv = binaryninja.open_view(fpath)

    print('functions = [')
    for function in bv.functions:
        print('{')
        print(f'    \'name\': \'{function.name}\',')
        print(f'    \'description\': \'{function}\',')
        print(f'    \'address\': 0x{function.start:X},')
        print(f'    \'instructions\': [')
        for bblock in sorted(function.basic_blocks, key=lambda bb: bb.start):
            addr = bblock.start
            for tokens, length in bblock:
                data = bv.read(addr, length)
                instxt = ''.join(t.text for t in tokens)
                print('        ' + (stringify(data) + ',').ljust(48) + '# ' + instxt)
                addr += length
        print(f'    ],')
        print(f'    \'length\': 0x{addr - function.start:X}')
        print('},')

    print(']')

