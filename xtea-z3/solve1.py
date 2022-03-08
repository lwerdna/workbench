#!/usr/bin/env python
# solve 1 cycle (2 feistal rounds) of xtea with z3

import sys
import time
from z3 import *

def cycle0_round0(left, right, key0):
    return left + ((((right<<4) ^ (z3.LShR(right, 5))) + right) ^ (0x00000000 + key0))

def cycle0_round1(left, right, key3):
    return right + ((((left<<4) ^ (z3.LShR(left, 5))) + left) ^ (0x9E3779B9 + key3))

def make_encipher_expr(a0, b0, key0, key3, c0, c1):
    # convert all arguments to BitVecVal
    [a0, b0, c0, c1] = \
        [BitVecVal(x, 32) for x in [a0, b0, c0, c1]]

    a1 = BitVec('a1', 32)
    b1 = BitVec('b1', 32)

    return And(
        a1 == cycle0_round0(a0, b0, key0),
        b1 == cycle0_round1(a1, b0, key3),
        c0 == a1,
        c1 == b1
    )

key0 = BitVec('key0', 32)
key3 = BitVec('key3', 32)
s = Solver()
s.add(make_encipher_expr(0x00112233, 0x44556677, key0, key3, 0x8BDC52EC, 0x3391FF02));
#s.add(key0 != 0x00010203)

print(s.sexpr())
assert s.check() == z3.sat
m = s.model()
name2var = {v.name(): v for v in m.decls()}
name2val = {name: m[var].as_long() for (name, var) in name2var.items()}
print('key: %08X-%08X-%08X-%08X' % (name2val['key0'], 0, 0, name2val['key3']))
