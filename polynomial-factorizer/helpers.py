#!/usr/bin/env python

# implementation of univariate polynomials
#
# uses [c0, c1, ..., c<degree>] internal representation, eg:
#     133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11
# has representation:
#     [11, 46, 111, 212, 233, 214, 133]

import re

from fractions import Fraction

#------------------------------------------------------------------------------
# PARSE / STRING CONVERSION
#------------------------------------------------------------------------------

class Polynomial():
    def __init__(self, initializer):
        self.coefficients = [Fraction(0)]

        if type(initializer) == str:
            self.parse(initializer)
        elif type(initializer) == list:
            self.coefficients = [Fraction(x) for x in initializer]
        elif type(initializer) == Fraction:
            self.coefficients = [initializer]
        elif type(initializer) == int:
            self.coefficients = [Fraction(initializer)]
        else:
            breakpoint()

    def parse(self, string):
        lookup = {}
        for term in string.split(' + '):
            # 214x^5
            if m := re.match(r'^(-?\d+)[a-zA-Z]\^(\d+)$', term):
                coeff, exp = m.group(1, 2)
            # x^5
            elif m := re.match(r'^[a-zA-Z]\^(\d+)$', term):
                coeff, exp = 1, m.group(1)
            # 214x
            elif m := re.match(r'^(-?\d+)[a-zA-Z]$', term):
                coeff, exp = m.group(1), 1
            # x
            elif m := re.match(r'^[a-zA-Z]$', term):
                coeff, exp = 1, 1
            # -x
            elif m := re.match(r'^-[a-zA-Z]$', term):
                coeff, exp = -1, 1
            # 133
            elif m := re.match(r'^(-?\d+)$', term):
                coeff, exp = m.group(1), 0
            else:
                breakpoint()

            coeff, exp = Fraction(coeff), int(exp)

            lookup[exp] = coeff

        degree = max(lookup)
        self.coefficients = [0] * (degree + 1)

        for degree, coeff in lookup.items():
            self.coefficients[degree] = coeff

    # get the coefficient for the degree-d term
    def coeff(self, d):
        return 0 if d > self.degree() else self.coefficients[d]

    def __eq__(self, rhs):
        if type(rhs) != Polynomial:
            rhs = Polynomial(rhs)

        da, db = self.degree(), rhs.degree()
        if da != db:
            return False
        return all(self.coefficients[i] == rhs.coefficients[i] for i in range(da+1))

    # internal representation to readable string
    def __str__(self):
        terms = []
        for deg, c in enumerate(self.coefficients):
            terms.append(f'{c}*x^{deg}')
        return ' + '.join(terms)

    #------------------------------------------------------------------------------
    # OPERATIONS
    #------------------------------------------------------------------------------
    def evaluate(self, x):
        result = Fraction(0)
        for e,c in enumerate(self.coefficients):
            result += c*(x**e)
        return result

    def degree(self):
        active_exps = [e for e,c in enumerate(self.coefficients) if c != 0]
        return 0 if not active_exps else max(active_exps)

    def normalize(poly):
        while self.coefficients and self.coefficients[-1] == 0:
            self.coefficients.pop()

    # do a coefficient-per-coefficient operation
    def dot_op(self, rhs, f):
        width = max(len(self.coefficients), len(rhs.coefficients))

        result = [None]*width
        for i in range(width):
            a = self.coefficients[i] if i < len(self.coefficients) else 0
            b = rhs.coefficients[i] if i < len(rhs.coefficients) else 0
            result[i] = f(a, b)

        while len(result)>1 and result[-1] == 0:
            result.pop()

        return Polynomial(result)

    def __add__(self, rhs):
        return self.dot_op(rhs, lambda a,b: a + b)

    def __sub__(self, rhs):
        return self.dot_op(rhs, lambda a,b: a - b)

    def __mul__(self, rhs):
        result = [0]*(self.degree() + rhs.degree() + 1)

        for degA, cA in enumerate(self.coefficients):
            for degB, cB in enumerate(rhs.coefficients):
                result[degA + degB] += cA * cB

        return Polynomial(result)

    # returns (quotient, remainder)
    def __truediv__(self, rhs):
        if self.degree() < rhs.degree():
            return (0, self)

        if self.degree() == rhs.degree():
            ratio = self.coefficients[-1] / rhs.coefficients[-1]
            return (Polynomial(ratio), self - (rhs * Polynomial(ratio)))

        shift = self.degree() - rhs.degree()
        quotient = Polynomial([0]*shift + [1])

        q, r = self / (rhs * quotient)
        quotient = quotient * q

        q, r = r / rhs
        return quotient + q, r

# Lagrange interpolation
def interpolate(points):
    result = Polynomial([0])

    for i,p in enumerate(points):
        # form a polynomial that is 0 at all points _OTHER THAN_ p
        basis = Polynomial([1])
        for x,y in [points[j] for j in range(len(points)) if j != i]:
            basis = basis * Polynomial([-x, 1])

        # make the polynomial the correct value at p
        x,y = p
        basis = basis * Polynomial([y/basis.evaluate(x)])

        # add this into the result
        result = result + basis

    return result

if __name__ == '__main__':
    print('TEST MODE!')

    a = Polynomial('x^2 + 2x + 3')
    b = Polynomial('4x + 5')
    c = Polynomial('x^2 + 6x + 8')
    assert a + b == Polynomial('x^2 + 6x + 8')
    assert a - b == Polynomial('x^2 + -2x + -2')
    c = Polynomial('4x^3 + 13x^2 + 22x + 15')
    assert c.evaluate(-1) == 2
    assert c.evaluate(0) == 15
    assert c.evaluate(1) == 54
    assert a*b == c
    assert c / a == (b, 0)
    assert c / b == (a, 0)

    a = Polynomial('x^2 + 1')
    b = Polynomial('x + 1')
    assert a + b == Polynomial('x^2 + x + 2')
    assert a - b == Polynomial('x^2 + -x')
    c = Polynomial('x^3 + x^2 + x + 1')
    assert c.evaluate(-1) == 0
    assert c.evaluate(0) == 1
    assert c.evaluate(1) == 4
    assert a*b == c
    assert c / a == (b, 0)
    assert c / b == (a, 0)

    a = Polynomial('7x^3 + 5x^2 + 3x + 1')
    b = Polynomial('19x^3 + 17x^2 + 13x + 11')
    assert a + b == Polynomial('26x^3 + 22x^2 + 16x + 12')
    assert a - b == Polynomial('-12x^3 + -12x^2 + -10x + -10')
    c = Polynomial('133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11')
    assert c.evaluate(-1) == 16
    assert c.evaluate(0) == 11
    assert c.evaluate(1) == 960
    assert a*b == c
    assert c / a == (b, 0)
    assert c / b == (a, 0)

    a = interpolate([(-1,2), (0,3), (1,6)])
    assert a == Polynomial('x^2 + 2x + 3')

    a = interpolate([(1,1), (2,2), (3,3), (4,4), (5,5), (6,6)])
    c = Polynomial('x')
    assert a == Polynomial('x')

    a = interpolate([(2,3), (5,7), (11,13), (17,19), (23,29), (31,41)])
    assert a.evaluate(2) == 3
    assert a.evaluate(5) == 7
    assert a.evaluate(11) == 13
    assert a.evaluate(17) == 19
    assert a.evaluate(23) == 29
    assert a.evaluate(31) == 41

