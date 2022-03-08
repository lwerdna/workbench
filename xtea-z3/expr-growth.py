#!/usr/bin/env python

# demonstrate how quickly expressions for ciphertext complicate as the cycles/rounds are increased

from z3 import *

key0 = BitVec('key0', 32)
key1 = BitVec('key1', 32)
key2 = BitVec('key2', 32)
key3 = BitVec('key3', 32)

a0 = BitVecVal(0x00112233, 32)
b0 = BitVecVal(0x44556677, 32)

# cycle 1/32
a1 = a0 + ((((b0<<4) ^ (z3.LShR(b0, 5))) + b0) ^ (0x00000000 + key0))
b1 = b0 + ((((a1<<4) ^ (z3.LShR(a1, 5))) + a1) ^ (0x9E3779B9 + key3))
print('---- A1 ----')
print(simplify(a1))

# cycle 2/32
a2 = a1 + ((((b1<<4) ^ (z3.LShR(b1, 5))) + b1) ^ (0x9e3779b9 + key1))
b2 = b1 + ((((a2<<4) ^ (z3.LShR(a2, 5))) + a2) ^ (0x3C6EF372 + key2))
print('---- A2 ----')
print(simplify(a2))

# cycle 3/32
a3 = a2 + ((((b2<<4) ^ (z3.LShR(b2, 5))) + b2) ^ (0x3C6EF372 + key2))
b3 = b2 + ((((a3<<4) ^ (z3.LShR(a3, 5))) + a3) ^ (0xDAA66D2B + key1)),
print('---- A3 ----')
print(simplify(a3))

