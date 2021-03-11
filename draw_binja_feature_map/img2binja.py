#!/usr/bin/env python
#
# 2019-08-16
#
# convert images to Binary Ninja "feature map" images
#
# please share enhancements and cool images you make with andrewl on binja slack
#
# instructions (requires ImageMagick and Netwide Assembler (nasm)):
#
# resize to 128 pixel width:
# $ convert -resize 128 input.png output.png
#
# convert image to black and white with dithering
# $ convert input.jpg -remap pattern:gray50 output.png
#
# run this script to produce out.asm
# $ ./img2binja.py input.jpg
#
# 4) assemble out.asm to whatever binary you want:
# $ nasm -f elf out.asm -o out.elf

import sys
from PIL import Image

im = Image.open(sys.argv[1])
im = im.convert('RGB')

binsize = 0
labelidx = 0
dataidx = 0
asm = []
asm.append('section .text')
asm.append('global _start')

# convert all pixels
for y in range(im.height):
	for x in range(im.width):
		px = im.getpixel((x,y))
		# black pixels are orphan null bytes
		if px == (0,0,0):
			asm.append('db 0')
			binsize += 1
		# white pixels are small functions
		elif px == (255,255,255):
			asm.append('loc_%d:' % labelidx)
			asm.append('ret')
			binsize += 1
			labelidx += 1
		else:
			raise Exception('non black or white color detected:', px)

# for all labels created, generate call
asm.append('_start:')
for i in range(labelidx):
	asm.append('call loc_%d' % i)
	binsize += 5 # e8 XX XX XX XX
asm.append('ret')
binsize += 1

# pad file size to get 128-byte scanlines
if 70000 - binsize > 0:
	asm.append('resb %d' % (70000 - binsize))

# write asm to file
with open('out.asm', 'w') as fp:
	fp.write('\n'.join(asm))

