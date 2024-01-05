#!/usr/bin/env python

from sympy import Rational, sqrt, I, re, im

from matrix import Matrix

def complex_modulus(c):
    return sqrt(re(c)**2 + im(c)**2)

def modulus_squares(M):
    return M.map(lambda c,i,j: complex_modulus(c)**2 + 0j)


X = Matrix(vals = [[1], [0], [0], [0], [0], [0], [0], [0]])

P = Matrix(vals = [ [ 0, 0, 0, 0, 0, 0, 0, 0 ],
                    [ 1/sqrt(2), 0, 0, 0, 0, 0, 0, 0 ],
                    [ 1/sqrt(2), 0, 0, 0, 0, 0, 0, 0 ],
                    [ 0, (-1 + I)/sqrt(6), 0, 1, 0, 0, 0, 0 ],
                    [ 0, (-1 - I)/sqrt(6), 0, 0, 1, 0, 0, 0 ],
                    [ 0, (1 - I)/sqrt(6), (-1 + I)/sqrt(6), 0, 0, 1, 0, 0 ],
                    [ 0, 0, (-1 - I)/sqrt(6), 0, 0, 0, 1, 0 ],
                    [ 0, 0, (1 - I)/sqrt(6), 0, 0, 0, 0, 1 ] ])

if __name__ == '__main__':
    # > The modulus squared of the P matrix is exactly the same as the bullets matrix. i.e., |p[i,j]|^2 = B
    from double_slit_bullets import B
    assert modulus_squares(P) == B

    for i in range(3): # after 2 nothing changes
        print(f'Photon position at t={i}:')
        #print(X)
        print(modulus_squares(X))
        X = P*X

# > This matrix is not a unitary matrix. Looking carefully at row 0, one can immediately see that P is not unitary. In our graph, there is nothing entering vertex 0. The reason why this matrix fails to be unitary is because we have not put in all the arrows in our graph. There are many more possible ways the photon can travel in a real-life physical situation. In particular, the photon might go from the right to the left. The diagram and matrix would become too complicated if we put in all the transitions. We are simply trying to demonstrate the interference phenomenon and we can accomplish that even with a matrix that is not quite unitary.
