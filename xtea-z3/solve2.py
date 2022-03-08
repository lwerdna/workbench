#!/usr/bin/env python

# solve 2 cycles (4 feistel rounds) of xtea with z3
import sys, time
from z3 import *

tmp_name_idx = -1
def get_tmp_name():
    global tmp_name_idx
    tmp_name_idx += 1
    return f't{tmp_name_idx}'

def make_encipher_expr(a0, b0, key0, key1, key2, key3, c0, c1):
    # convert all arguments to BitVecVal
    [a0, b0, c0, c1] = \
        [BitVecVal(x, 32) for x in [a0, b0, c0, c1]]

    a1 = BitVec(get_tmp_name(), 32)
    b1 = BitVec(get_tmp_name(), 32)
    a2 = BitVec(get_tmp_name(), 32)
    b2 = BitVec(get_tmp_name(), 32)

    return And(
        a1 == a0 + ((((b0<<4) ^ (z3.LShR(b0, 5))) + b0) ^ (0x00000000 + key0)),
        b1 == b0 + ((((a1<<4) ^ (z3.LShR(a1, 5))) + a1) ^ (0x9E3779B9 + key3)),
        a2 == a1 + ((((b1<<4) ^ (z3.LShR(b1, 5))) + b1) ^ (0x9e3779b9 + key1)),
        b2 == b1 + ((((a2<<4) ^ (z3.LShR(a2, 5))) + a2) ^ (0x3C6EF372 + key2)),
        c0 == a2,
        c1 == b2
    )

key0 = BitVec('key0', 32)
key1 = BitVec('key1', 32)
key2 = BitVec('key2', 32)
key3 = BitVec('key3', 32)
s = Solver()
s.add(make_encipher_expr(0x00112233, 0x44556677, key0, key1, key2, key3, 0x5A055406, 0xEC8F42BD))
s.add(make_encipher_expr(0xAAAAAAAA, 0xBBBBBBBB, key0, key1, key2, key3, 0x9BE82231, 0xA67A3F1D))
s.add(make_encipher_expr(0xCCCCCCCC, 0xDDDDDDDD, key0, key1, key2, key3, 0xB6B4E456, 0xB5A0992D))
print(s.sexpr())

while True:
    print(s.check())
    if s.check() != z3.sat:
        break
    m = s.model()
    name2var = {v.name(): v for v in m.decls()}
    name2val = {name: m[var].as_long() for (name, var) in name2var.items()}
    print('key: %08X-%08X-%08X-%08X' % (name2val['key0'], name2val['key1'], name2val['key2'], name2val['key3']))

    s.add(key0 != name2val['key0'])
