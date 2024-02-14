#!/usr/bin/env python
#
# factor polynomials over GF(2) using z3
# solve for variables that select which possible partial products are active in the final sum
#
# original work: Yurichev's SAT_SMT_by_example 13.3 Factorize GF(2)/CRC

import sys
import time
import operator, functools
from z3 import *

def bit_count(x):
    count = 0
    while x:
        count += 1
        x >>= 1
    return count

# return a larger BitVec formed by shifting a smaller BitVec left
def bv_shl(bv, shamt, width):
    head = width - (bv.size() + shamt)
    assert head >= 0

    result = bv
    if shamt:
        result = Concat(result, BitVecVal(0, shamt))
    if head:
        result = Concat(BitVecVal(0, head), result)

    return result

def factoring_solver(poly):
    INPUT_SIZE = bit_count(poly)
    OUTPUT_SIZE = 2*INPUT_SIZE

    s = Solver()

    # input factors
    a = BitVec('a', INPUT_SIZE)
    b = BitVec('b', INPUT_SIZE)

    # partial products
    p = [BitVec('p_%d' % i, OUTPUT_SIZE) for i in range(INPUT_SIZE)]

    # bits in b select with shifted a's are active in the sum
    for i in range(INPUT_SIZE):
        s.add(p[i] == If(Extract(i, i, b)==1, bv_shl(a, i, OUTPUT_SIZE), 0))

    # form expression like s.add(p[0] ^ p[1] ^ ... ^ p[OUTPUT_SIZE-1] == poly)
    s.add(functools.reduce(operator.xor, p) == poly)

    # no trivial solutions
    s.add(a != 1)
    s.add(b != 1)

    return s

tests = [
    # from http://mathworld.wolfram.com/IrreduciblePolynomial.html
    7, # irreducible
    5, # reducible
    # from Colbourn, Dinitz - Handbook of Combinatorial Designs (2ed, 2007), p.809: 
    0b10000001001, # irreducible
    0b10000001111, # irreducible
    # MSB is always 1 in CRC polynomials, and it's omitted
    # but we add it here (leading 1 bit):
    0x18005, # CRC-16-IBM, reducible
    0x11021, # CRC-16-CCITT, reducible
    0x1C867, # CRC-16-CDMA2000, irreducible
    0x104c11db7, # CRC-32, irreducible
    0x11EDC6F41, # CRC-32C (Castagnoli), CRC32 x86 instruction, reducible
    0x1741B8CD7, # CRC-32K (Koopman {1,3,28}), reducible
    0x132583499, # CRC-32K2 (Koopman {1,1,30}), reducible
    0x1814141AB # CRC-32Q, reducible
]

for poly in tests:
    s = factoring_solver(poly)

    t0 = time.time()
    print('factoring 0x%X' % poly)
    result = s.check()
    print('  solving took %fs' % (time.time() - t0))

    if result == unsat:
        print('  prime')
    else:
        m = s.model()
        result = {v.name(): m[v].as_long() for v in m.decls()}
        (a, b) = (result['a'], result['b'])
        print("  composite, factors: 0x%x, 0x%x" % (a, b))

        print("  verifying...", end='')
        check = 0
        while b:
            if b & 1:
                check = check ^ a
            b >>= 1
            a <<= 1
        if check == poly:
            print('PASS: 0x%X == 0x%X' % (check, poly))
        else:
            print('FAIL: 0x%X != 0x%X' % (check, poly))
            sys.exit(-1)

    print('')
