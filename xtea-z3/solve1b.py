#!/usr/bin/env python
# solve 1 cycle (2 feistal rounds) of xtea with z3

import sys
import time
from z3 import *

s = Solver()

key0 = BitVec('key0', 32)
key3 = BitVec('key3', 32)

a0 = BitVec('a0', 32)
b0 = BitVec('b0', 32)

a1 = BitVec('a1', 32)
s.add(a1 == a0 + ((((b0<<4) ^ (z3.LShR(b0, 5))) + b0) ^ (0x00000000 + key0)))
b1 = BitVec('b1', 32)
s.add(b1 == b0 + ((((a1<<4) ^ (z3.LShR(a1, 5))) + a1) ^ (0x9E3779B9 + key3)))

# WORKS:
s.add(And(a0 == 0x00112233, b0 == 0x44556677, a1 == 0x8BDC52EC, b1 == 0x3391FF02))
# DOESN'T WORK:
#s.add(Implies(And(a0 == 0x00112233, b0 == 0x44556677), And(a1 == 0x8BDC52EC, b1 == 0x3391FF02)))


print(s.sexpr())
assert s.check() == z3.sat
m = s.model()
name2var = {v.name(): v for v in m.decls()}
name2val = {name: m[var].as_long() for (name, var) in name2var.items()}
print('key: %08X-%08X-%08X-%08X' % (name2val['key0'], 0, 0, name2val['key3']))
