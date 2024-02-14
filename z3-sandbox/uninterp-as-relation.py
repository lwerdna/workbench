#!/usr/bin/env python

# from TU Graz presentation by Vedad Hadzic

from z3 import Solver, Int, IntSort, BoolSort, Function
from z3 import ForAll, And, Or, Not, Implies, sat as SAT

# create an integer and a function
x = Int("x")
f = Function("f", IntSort(), IntSort(), BoolSort())

solver = Solver()

solver.add( ForAll([x], Implies(And(x > 0, x < 4), f(x, x))) )
solver.add( ForAll([x], Implies(Or(x <= 0, x >= 4), Not(f(x, x)))) )

if solver.check() != SAT:
    exit(1)

m = solver.model()

print(f'f(0,0)={m.eval(f(0,0))}')
print(f'f(1,2)={m.eval(f(1,2))}')
print(f'f(2,3)={m.eval(f(2,3))}')
print(f'f(3,3)={m.eval(f(3,3))}')

for i in range(0,5):
    # assert ∀ x in (0,4). f(x,x) = 1 # check if satisfiable
    # get the solution
    # print the relation table
    vs = [int(bool(m.eval(f(i, j)))) for j in range(0,5)]
    print(f'i={i} ' + ("%d " * 5) % tuple(vs))     # print one row

