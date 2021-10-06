#!/usr/bin/env python

# Bailey–Borwein–Plouffe formula
# https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula

import os, sys, re, pprint

def compute(n):
    result = 0
    for k in range(n):
        result += (1/16**k)*(4/(8*k+1)-2/(8*k+4)-1/(8*k+5)-1/(8*k+6))
    return result

for i in range(100):
    print('%d: %.16f' % (i, compute(i)))
