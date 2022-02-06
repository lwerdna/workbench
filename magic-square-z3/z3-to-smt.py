#!/usr/bin/env python

# https://theory.stanford.edu/~nikolaj/programmingz3.html
from z3 import *
Tie, Shirt = Bools('Tie Shirt')
s = Solver()
#s.smtlib2_log = './test.smt2'
s.set('smtlib2_log', './test.smt2')
s.add(Or(Tie, Shirt), 
      Or(Not(Tie), Shirt), 
      Or(Not(Tie), Not(Shirt)))

# to screen
print(s.sexpr())

#print(s.check())
#print(s.model())


