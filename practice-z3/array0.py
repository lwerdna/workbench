#!/usr/bin/env python

from z3 import *


# simple array from https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-intro
A = Array('A', IntSort(), IntSort())
x, y = Ints('x y')
solve(A[x] == x, Store(A, x, y) == A)

# solution
# [A = Store(K(Int, 2), 3, 3), x = 3, y = 3]
#
# means A is an array formed by
#   storing 3 at location 3 in
#     an array keyed with Int that always returns 2
#
#             A: [...2, 2, 2, 2, 2, 3, 2, 2, 2, ...]
#       indices: [  -2 -1  0  1  2  3  4  5  6
#
# and x = 3
# and y = 3

x = Int('x')
y = Int('y')
n = x + y >= 3
print("num args: ", n.num_args())
print("children: ", n.children())
print("1st child:", n.arg(0))
print("2nd child:", n.arg(1))
print("operator: ", n.decl())
print("op name:  ", n.decl().name())

# imagine [ 4, 2, 3, 0, 1 ]
#           0  1  2  3  4
#

A = Array('A', IntSort(), IntSort())
a,b,c,d = Ints('a b c d')
foo = solve(A[A[A[A[A[4]]]]] == 4)

# [A = Store(Store(Store(Store(K(Int, 4), 3, 5), 4, 2), 2, 3),
#           5,
#           6)]
#
# K(Int, 4) =  [..., 4, 4, 4, 4, 4, 4, 4, ...]
# at [3] = 5
# at [4] = 2
# at [2] = 3
# at [5] = 6

#           1  2  3  4  5  6
# so [...4, 4, 3, 5, 2, 6, 4, 4, ...]

# and it works, cool

# what about negative indices?
# [ 2, 0, 1, 999, -1]
#  -2 -1  0    1   2
A = Array('A', IntSort(), IntSort())
a,b,c,d = Ints('a b c d')
solve(A[A[A[A[A[-2]]]]] == 999)

#[A = Store(Store(Store(Store(K(Int, 5), -2, 2), 3, 4),
#                 5,
#                 999),
#           2,
#           3)]

# -2: 2
# -1: 5
#  0: 5
#  1: 5
#  2: 3
#  3: 4
#  4: 5
#  5: 999

#A = Array('A', BitVecSort(64), BitVecSort(64))
#x = BitVecVal(4, 64)
#foo = solve(A[A[A[A[A[x]]]]] == 4)
