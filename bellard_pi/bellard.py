#!/usr/bin/env python

# Bellard's formula
# https://en.wikipedia.org/wiki/Bellard%27s_formula

import os, sys, re, pprint

def compute(limit):
    result = 0
    for n in range(limit):
        a = (-1)**n / 2**(10*n)
        b = -32 / (4*n+1)
        c = -1 / (4*n+3)
        d = 256 / (10*n+1)
        e = -64 / (10*n+3)
        f = -4 / (10*n+5)
        g = -4 / (10*n+7)
        h = 1 / (10*n+9)
        result += a * (b+c+d+e+f+g+h)
    result = result / 64
    return result

for i in range(100):
    print('%d: %.16f' % (i, compute(i)))
