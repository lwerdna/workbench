#!/usr/bin/env python3

import sys
import struct
import crcsolver

func = lambda x: crcsolver.compute(x, {'width':32, 'poly':0xffffffff, 'init':0xffffffff, 'refin':True, 'refout':True, 'xorout':0xffffffff})

target_crc = 0

start = int(sys.argv[1], 16)
end = int(sys.argv[2], 16)
length = end - start

for target_crc in range(start, end):
    input_ = crcsolver.solve(b'____', range(32), target_crc, func)
    #print('input: ', input_)
    
    if func(input_) == target_crc:
        #print('SUCCESS!')
        pass
    else:
        print('no input for target_crc=%08X' % target_crc)
        sys.exit(-1)

    if target_crc & 0xFF == 0:
        print('solver [%08X, %08X) is at %08X, %.02f%% done' % (start, end, target_crc, (target_crc-start)/length))
