#!/usr/bin/env python

# will constraining the values of the variables aid in determining satisfiability? YES

import z3

a0, a1, a2 = z3.Ints('a0, a1, a2')
b0, b1, b2, b3, b4 = z3.Ints('b0, b1, b2, b3, b4')

s = z3.SolverFor('LIA') # linear integer arithmetic
s.add(a0*b0 == 11)
s.add(a0*b1 + a1*b0 == 46)
s.add(a0*b2 + a1*b1 + a2*b0 == 111)
s.add(a0*b3 + a1*b2 + a2*b1 == 212)
s.add(a0*b4 + a1*b3 + a2*b2 == 233)
s.add(a1*b4 + a2*b3 == 214)
s.add(a2*b4 == 133)

s.add(a0 >= 0); s.add(a0 < 20)
s.add(a1 >= 0); s.add(a1 < 20)
s.add(a2 >= 0); s.add(a2 < 20)
s.add(b0 >= 0); s.add(b0 < 20)
s.add(b1 >= 0); s.add(b1 < 20)
s.add(b2 >= 0); s.add(b2 < 20)
s.add(b0 >= 0); s.add(b0 < 20)

s.check()

print('DONE')
