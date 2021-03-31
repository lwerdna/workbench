#!/usr/bin/env python

# generate a long version of hello.s to exercise adrp/add
# ARM64_RELOC_PAGE21/ARM64_RELOC_PAGEOFF12 relocations

# ./gen.py > hello_big.s

import random

print('.global _start')
print('.align 2')
print('_start:')

# want 3.5 pages, or 14k bytes
# each instruction is 4 bytes, or 3.5k instructions
instrs = [0] * int(3.5 * 1024)

count = 0
while count < 100:
	i = random.randint(0, len(instrs)-1)
	# generated i within bounds
	if not (i<len(instrs) and (i+1)<len(instrs)):
		continue
	# must contain nop
	if instrs[i] or instrs[i+1]:
		continue
	instrs[i] = 1
	instrs[i+1] = 1
	count += 1

for x in instrs:
	if x:
		print('\tadrp	x1, helloworld@PAGE')
		print('\tadd	x1, x1, helloworld@PAGEOFF')
	else:
		print('\tnop')

print('\tmov		x0, #1')
print('\tmov		x2, #13')
print('\tmov		x16, #4')
print('\tsvc		#0x80')
print('\tmov		x0, #0')
print('\tmov		x16, #1')
print('\tsvc		#0x80')
print('\tret')

print('helloworld:')
print('\t.ascii  "Hello World!\\n"')



	

