#!/usr/bin/env python

import os, sys
import hashlib

import binaryninja

counts = [0]*256

if __name__ == '__main__':
    fpath = sys.argv[1] if sys.argv[1:] else '../testbins/md5/md5_x64-macos'

    bv = binaryninja.load(fpath)

    for function in bv.functions:
        for bblock in function.basic_blocks:
            for b in bv.read(bblock.start, len(bblock)):
                counts[b] += 1

    print('Byte,Count')
    for i,count in enumerate(counts):
        print(f'{i:02X},{count}')

    print('')

    print(f'# byte distribution for: {fpath}')
    md5 = hashlib.md5(open(fpath,'rb').read()).hexdigest()
    print(f'# md5: {md5}')
    #total = sum(counts)
    #distrib = [round(c/total,4) for c in counts]
    print(f'counts_{bv.arch.name} = {counts}')
