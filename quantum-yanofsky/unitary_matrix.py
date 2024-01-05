#!/usr/bin/env python

import copy
from sympy import re, im, sqrt, conjugate, I

def complex_modulus(c):
    return sqrt(re(c)**2 + im(c)**2)

class Matrix:
    def __init__(self, n_rows, n_cols):
        self.values = []
        
        for i in range(n_rows):
            self.values.append([None]*n_cols)

    def load(self, values):
        self.values = values

    def dims(self):
        return len(self.values), len(self.values[0])

    # applies a function to each element in the matrix
    def map(self, func):
        n_rows, n_cols = self.dims()

        values = copy.deepcopy(self.values)
        for i in range(n_rows):
            for j in range(n_cols):
                values[i][j] = func(self.values[i][j], i, j)

        result = Matrix(n_rows, n_cols)
        result.load(values)
        return result

    def transpose(self):
        n_rows, n_cols = self.dims()
        return Matrix(n_cols, n_rows).map(lambda c,i,j: self.values[j][i])

    def modulus_squares(self):
        return self.map(lambda c,i,j: complex_modulus(c)**2 + 0j)

    def conjugate_transpose(self):
        return self.transpose().map(lambda c,i,j: conjugate(c))

    def __str__(self):
        lines = []
        for row in self.values:
            lines.append(', '.join(str(k) for k in row))
        return '\n'.join(lines)

U = Matrix(3, 3)

U.load(     [   [1/sqrt(2), 1/sqrt(2), 0],
                [-1*I/sqrt(2), -1*I/sqrt(2), 0],
                [0, 0, I]
            ]
        )
print(U)
print('----')

U_squared = U.modulus_squares()

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

U_dagger = U.conjugate_transpose()
print(U_dagger)
print('----')
