#!/usr/bin/env python

import math

def complex_modulus(c):
    return math.sqrt(c.real**2 + c.imag**2)

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

        values = list(self.values)
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
        return self.tranpose().map(lambda c,i,j: c.conjugate())

    def __str__(self):
        lines = []
        for row in self.values:
            lines.append(', '.join(str(k) for k in row))
        return '\n'.join(lines)

foo = Matrix(3, 3)

foo.load(   [   [1/math.sqrt(2), 1/math.sqrt(2), 0],
                [-1j/math.sqrt(2), -1j/math.sqrt(2), 0],
                [0, 0, 1j]
            ]
        )
print(foo)

bar = foo.modulus_squares()

print(bar)

foo.load(   [   [1, 2],
                [3, 4],
                [5, 6]
            ]
        )
print(foo)

bar = foo.transpose()

print(bar)
