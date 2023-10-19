#!/usr/bin/env python

from pcode import A32ExpandImm_C, BitsN

encoding = 0xe3100001 # tst r0, #1
# 11100011000100000000000000000001

Rn = (encoding >> 16) & 0xF
imm12 = BitsN(encoding & 0xFFF, 12)
print(f'imm12: {imm12}')
imm32, carry = A32ExpandImm_C(imm12, 1)

print(f'Rn: {Rn:d}')
print(f'imm32: {imm32}')
print(f'carry: {carry}')
