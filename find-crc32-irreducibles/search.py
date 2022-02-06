#!/usr/bin/env python

import sympy
from sympy.polys.domains import ZZ
from sympy.polys.galoistools import gf_add, gf_mul, gf_rem

# [1, 1, 0, 0, 1] -> x^4 + x^3 + 1
def bits_to_poly(bits):
    x = sympy.symbols('x')
    
    result = 0
    for (e, b) in enumerate(reversed(bits)):
        if not b:
            continue
        result += x**e

    return result

def uint32_to_bits(value):
    result = []
    for i in range(32):
        result.append(value & 1)
        value >>= 1
    return list(reversed(result))

def uint32_to_poly(value, is_reversed=False):
    bits = uint32_to_bits(value)

    if is_reversed:
        bits = list(reversed(bits))

    return bits_to_poly(bits) + sympy.symbols('x')**32

def irreducible(poly):
    return sympy.factor(poly, modulus=2) == poly

if __name__ == '__main__':
#    x = sympy.symbols('x')
#    p = x**4 + x**2

#    print(sympy.factor(p, modulus=2))

    x = sympy.symbols('x')

    assert bits_to_poly([]) == 0
    assert bits_to_poly([1]) == 1
    assert bits_to_poly([1, 0]) == x
    assert bits_to_poly([1, 1]) == x + 1
    assert bits_to_poly([1, 0, 0]) == x**2
    assert bits_to_poly([1, 0, 1]) == x**2 + 1

    p0 = uint32_to_poly(0x04c11db7)
    assert p0 == x**32 + x**26 + x**23 + x**22 + x**16 + x**12 + x**11 + x**10 + x**8 + x**7 + x**5 + x**4 + x**2 + x + 1
    p1 = uint32_to_poly(0xEDB88320, True)
    assert p1 == x**32 + x**26 + x**23 + x**22 + x**16 + x**12 + x**11 + x**10 + x**8 + x**7 + x**5 + x**4 + x**2 + x + 1
   
    p2 = uint32_to_poly(0x12345678, True)

    p3 = uint32_to_poly(0xFFFFFFFF, True)

    p4 = uint32_to_poly(0x82345678, True)

    breakpoint()
