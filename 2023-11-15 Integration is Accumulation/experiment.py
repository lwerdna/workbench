#!/usr/bin/env python

from operator import add
from itertools import accumulate

c = [6]*10
d = list(accumulate(c, add))
e = list(accumulate(d, add))
f = list(accumulate(e, add))

print('d:')
for i,val in enumerate(d):
    print(f'{i},{val}')

print('e:')
for i,val in enumerate(e):
    print(f'{i},{val}')

print('f:')
for i,val in enumerate(f):
    print(f'{i},{val}')

c, d, e, f = 6, 0, 0, 0
for _ in range(10):
    d += c
    e += d
    f += e
    print(f)
