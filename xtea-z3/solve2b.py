#!/usr/bin/env python

# solve 2 cycles (4 feistel rounds) of xtea with z3
import sys, time
from z3 import *

s = Solver()

# input factors
key0 = BitVec('key0', 32)
key1 = BitVec('key1', 32)
key2 = BitVec('key2', 32)
key3 = BitVec('key3', 32)

# input vectors are equal to plaintext
a0 = BitVec('a0', 32)
b0 = BitVec('b0', 32)

# cycle 1/32
a1 = BitVec('a1', 32)
s.add(a1 == a0 + ((((b0<<4) ^ (z3.LShR(b0, 5))) + b0) ^ (0x00000000 + key0)))
b1 = BitVec('b1', 32)
s.add(b1 == b0 + ((((a1<<4) ^ (z3.LShR(a1, 5))) + a1) ^ (0x9E3779B9 + key3)))

# cycle 2/32
a2 = BitVec('a2', 32)
s.add(a2 == a1 + ((((b1<<4) ^ (z3.LShR(b1, 5))) + b1) ^ (0x9E3779B9 + key1)))
b2 = BitVec('b2', 32)
s.add(b2 == b1 + ((((a2<<4) ^ (z3.LShR(a2, 5))) + a2) ^ (0x3C6EF372 + key2)))

# output vectors must be equal to ciphertext
#s.add(And(a0 == 0x00112233, b0 == 0x44556677))
#s.add(And(a1 == 0x8BDC52EC, b1 == 0x3391FF02))
s.add(Implies(And(a0 == 0x00112233, b0 == 0x44556677), And(a1 == 0x8BDC52EC, b1 == 0x3391FF02)))
#s.add(Implies(And(a0 == 0x00112233, b0 == 0x44556677), And(a2 == 0x5A055406, b2 == 0xEC8F42BD)))

print(s.sexpr())

assert s.check() == z3.sat
m = s.model()
name2var = {v.name(): v for v in m.decls()}
name2val = {name: m[var].as_long() for (name, var) in name2var.items()}
print('key %08X-%08X-%08X-%08X' % (name2val['key0'], name2val['key1'], name2val['key2'], name2val['key3']))
