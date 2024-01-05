#!/usr/bin/env python

from sympy import Rational

from matrix import Matrix

X = Matrix(vals = [[1], [0], [0], [0], [0], [0], [0], [0]])

B = Matrix(vals = [ [ 0, 0, 0, 0, 0, 0, 0, 0 ],
                    [ Rational(1,2), 0, 0, 0, 0, 0, 0, 0 ],
                    [ Rational(1,2), 0, 0, 0, 0, 0, 0, 0 ],
                    [ 0, Rational(1,3), 0, 1, 0, 0, 0, 0 ],
                    [ 0, Rational(1,3), 0, 0, 1, 0, 0, 0 ],
                    [ 0, Rational(1,3), Rational(1,3), 0, 0, 1, 0, 0 ],
                    [ 0, 0, Rational(1,3), 0, 0, 0, 1, 0 ],
                    [ 0, 0, Rational(1,3), 0, 0, 0, 0, 1 ] ])

for i in range(5):
    print(f'Bullet position at t={i}:')
    print(X)
    X = B*X
