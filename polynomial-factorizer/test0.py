#!/usr/bin/env python

# demonstrate z3 spinning on a problem

import z3

a0, a1, a2 = z3.Ints('a0, a1, a2')
b0, b1, b2, b3, b4 = z3.Ints('b0, b1, b2, b3, b4')

s = z3.Solver()
s.add(a0*b0 == 11)
s.add(a0*b1 + a1*b0 == 46)
s.add(a0*b2 + a1*b1 + a2*b0 == 111)
s.add(a0*b3 + a1*b2 + a2*b1 == 212)
s.add(a0*b4 + a1*b3 + a2*b2 == 233)
s.add(a1*b4 + a2*b3 == 214)
s.add(a2*b4 == 133)

s.check()

print('DONE')
