#!/usr/bin/env python

from z3 import *

a = Bool('a')
b = Bool('b')
c = And(a, b)

# real abstractly, let's make a datatype called "List"
List = Datatype('List')

# first constructor: first we should be able to add an Int to an existing list
# or (Int, List) -> List

# arg0: constructor name "cons"
# arg1: name,sort of input0
# arg2: name,sort of input1
List.declare('cons', ('car', IntSort()), ('cdr', List))

# second constructor: nil takes no arguments and returns a List

# arg0: constructor name "nil"
# no further arguments means no
List.declare('nil')


