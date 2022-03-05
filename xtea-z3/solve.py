#!/usr/bin/env python
#

import sys
import time
from z3 import *

s = Solver()

# input factors

b0 = BitVec('b0', 32)
a0 = BitVec('a0', 32)

b1 = BitVec('b1', 32)
a1 = BitVec('a1', 32)

key0 = BitVec('key0', 32)
key1 = BitVec('key1', 32)
key2 = BitVec('key2', 32)
key3 = BitVec('key3', 32)

tmp = BitVec('tmp', 32)

# input vectors are equal to plaintext
s.add(a0 == 0x00112233)
s.add(b0 == 0x44556677)
# output vector

#	uint32_t a1 = a0 + ((((b0 << 4) ^ (b0 >> 5)) + b0) ^ 0x00010203);
#	uint32_t b1 = b0 + ((((a1 << 4) ^ (a1 >> 5)) + a1) ^ 0xAA4487C8);

#	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x00000000 + key[0]);
#	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x9E3779B9 + key[3]);
s.add(a1 == a0 + ((((b0<<4) ^ (b0>>5)) + b0) ^ (key0)))
s.add(b1 == b0 + ((((a1<<4) ^ (a1>>5)) + a1) ^ (key3)))
# output vectors must be equal to ciphertext
s.add(a1 == 0x8BDC52EC)
s.add(b1 == 0x3391FF02)
print(s.sexpr())

assert s.check() == z3.sat
print('SAT!')
m = s.model()
name2var = {v.name(): v for v in m.decls()}
name2val = {name: m[var].as_long() for (name, var) in name2var.items()}
print('key0: 0x%08X' % name2val['key0'])
print('key3: 0x%08X' % name2val['key3'])
