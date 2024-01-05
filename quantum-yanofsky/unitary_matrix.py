#!/usr/bin/env python

from sympy import re, im, sqrt, conjugate, I

from matrix import Matrix

def complex_modulus(c):
    return sqrt(re(c)**2 + im(c)**2)

def modulus_squares(M):
    return M.map(lambda c,i,j: complex_modulus(c)**2 + 0j)

def conjugate_transpose(M):
    return M.transpose().map(lambda c,i,j: conjugate(c))

U = Matrix(3, 3)

U.load(     [   [1/sqrt(2), 1/sqrt(2), 0],
                [-1*I/sqrt(2), -1*I/sqrt(2), 0],
                [0, 0, I]
            ]
        )
print(U)
print('----')

U_squared = modulus_squares(U)

print(U_squared)
print('----')

foo = Matrix(3, 2)
foo.load(   [   [1, 2],
                [3, 4],
                [5, 6]
            ]
        )
print(foo)
print('----')

bar = foo.transpose()

print(bar)
print('----')

U_dagger = conjugate_transpose(U)
print(U_dagger)
print('----')
