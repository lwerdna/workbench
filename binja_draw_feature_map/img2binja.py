#!/usr/bin/env python

import sys
from PIL import Image

im = Image.open(sys.argv[1])
im = im.convert('RGB')

binsize = 0
labelidx = 0
dataidx = 0
asm = []
asm.append('section .text')
asm.append('global _main')

# convert all pixels
for y in range(im.height):
    for x in range(im.width):
        px = im.getpixel((x,y))
        
        # greyscale has all three the same
        assert px[0] == px[1] == px[2]

        # black pixels are orphan null bytes
        if px[0] <= 127:
            asm.append('db 0')
            binsize += 1
        # white pixels are small functions
        else:
            asm.append('loc_%d:' % labelidx)
            asm.append('ret')
            binsize += 1
            labelidx += 1

# for all labels created, generate call
asm.append('_main:')
for i in range(labelidx):
    asm.append('call loc_%d' % i)
    binsize += 5 # e8 XX XX XX XX
asm.append('ret')
binsize += 1

# pad file size to get 128-byte scanlines
if 70000 - binsize > 0:
    asm.append('resb %d' % (70000 - binsize))

print('\n'.join(asm))

