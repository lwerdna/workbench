#!/usr/bin/env python

# generate disassembly test cases by analyzing a file

import os, sys, re

import binaryninja

if __name__ == '__main__':
    fpath = sys.argv[1] if sys.argv[1:] else '../testbins/md5/md5_x64-macos'

    bv = binaryninja.load(fpath)

    samples_per_mnemonic = 4

    # {
    # 'foo': [(addr:int, encoding:str, disassembly:str), ...]
    # ...
    # }
    lookup = {}

    for function in bv.functions:
        for bblock in sorted(function.basic_blocks, key=lambda bb: bb.start):
            addr = bblock.start
            for tokens, length in bblock:
                addr_here = addr
                addr = addr + length

                mnemonic = tokens[0].text
                if not mnemonic in lookup:
                    lookup[mnemonic] = []

                if len(lookup[mnemonic]) >= samples_per_mnemonic:
                    continue

                data = bv.read(addr_here, length).hex()

                # if we already have this sample, skip it
                if [entry for entry in lookup[mnemonic] if entry[1]==data]:
                    continue

                instxt = ''.join(t.text for t in tokens)
                instxt = re.sub(r'\s+', ' ', instxt)

                lookup[mnemonic].append((addr_here, data, instxt))

    print(f'# generated using {sys.argv[0]} on file {fpath}')
    print('tests = [')
    for mnemonic, samples in lookup.items():
        for addr, encoding, distxt in samples:
            print(f"    ({hex(addr)}, '{encoding}', '{distxt}'),")
    print(']')

