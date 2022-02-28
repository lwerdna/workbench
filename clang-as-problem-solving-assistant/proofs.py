#!/usr/bin/env python

from z3 import *

a = Int('a')
E = Implies(a % 4 == 0, a % 2 == 0)
prove(E)

x = Real('x')
E = Implies(And(x != 4, (2*x - 5)/(x - 4) == 3), x == 7)
prove(E)

x = Int('x')
E = Implies(And(x != 4, (2*x - 5)/(x - 4) == 3), x == 7)
prove(E)

x = Int('x')
a = 2*x - 5
b = x - 4
E = Implies(And(x != 4, a%b == 0, a/b == 3), x == 7)
prove(E)
