#!/usr/bin/env python

# implementation of univariate polynomials
#
# uses [c0, c1, ..., c<degree>] internal representation, eg:
#     133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11
# has representation:
#     [11, 46, 111, 212, 233, 214, 133]

import re

#------------------------------------------------------------------------------
# PARSE / STRING CONVERSION
#------------------------------------------------------------------------------

# parse strings to internal representation
def parse(pstr):
    lookup = {}
    for term in pstr.split(' + '):
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

        coeff, exp = int(coeff), int(exp)

        lookup[exp] = coeff

    degree = max(lookup)
    result = [0] * (degree + 1)

    for degree, coeff in lookup.items():
        result[degree] = coeff

    return result

# internal representation to readable string
def unparse(poly):
    terms = []
    for (deg, coeff) in enumerate(poly):
        if coeff == 0:
            continue
        if deg == 0: e_str = ''
        elif deg == 1: e_str = 'x'
        else: e_str = f'x^{deg}'
        c_str = '' if (coeff == 1 and e_str) else f'{coeff}'
        terms.append(f'{c_str}{e_str}')
    return ' + '.join(reversed(terms))

#------------------------------------------------------------------------------
# OPERATIONS
#------------------------------------------------------------------------------

def evaluate(poly, x):
    result = 0
    for e,c in enumerate(poly):
        result += c*(x**e)
    return result

def degree(poly):
    return len(poly)-1

def normalize(poly):
    while poly and poly[-1] == 0:
        poly = poly[0:-1]
    #poly = [int(x) for x in poly]
    return poly

def add(a, b):
    width = max(len(a), len(b))
    a = a + [0] * (width - len(a))
    b = b + [0] * (width - len(b))
    return normalize([a[i]+b[i] for i in range(width)])

def sub(a, b):
    width = max(len(a), len(b))
    a = a + [0] * (width - len(a))
    b = b + [0] * (width - len(b))
    return normalize([a[i]-b[i] for i in range(width)])

def mult(poly_a, poly_b):
    result = [0]*(degree(poly_a) + degree(poly_b) + 1)

    for (degA, cA) in enumerate(poly_a):
        for (degB, cB) in enumerate(poly_b):
            result[degA + degB] += cA * cB

    return normalize(result)

# returns (quotient, remainder)
def divide(a, b):
    if degree(a) < degree(b):
        return (0, a)

    if degree(a) == degree(b):
        ratio = a[-1] / b[-1]
        return ([ratio], sub(a, mult(b, [ratio])))

    shift = degree(a) - degree(b)
    quotient = [0]*shift + [1]

    q, r = divide(a, mult(b, quotient))
    quotient = mult(quotient, q)

    q, r = divide(r, b)
    return (add(quotient, q), r)

# Lagrange interpolation
def interpolate(points):
    result = []

    for i,p in enumerate(points):
        # form a polynomial that is 0 at all points _OTHER THAN_ p
        basis = [1]
        for x,_ in [points[j] for j in range(len(points)) if j != i]:
            basis = mult(basis, [-x, 1])
        # make the polynomial the correct value at p
        basis = mult(basis, [p[1]/evaluate(basis, p[0])])

        # add this into the result
        result = add(result, basis)

    return result

if __name__ == '__main__':
    print('TEST MODE!')

    a = parse('x^2 + 2x + 3')
    b = parse('4x + 5')
    assert add(a, b) == parse('x^2 + 6x + 8')
    assert sub(a, b) == parse('x^2 + -2x + -2')
    c = parse('4x^3 + 13x^2 + 22x + 15')
    assert evaluate(c, -1) == 2
    assert evaluate(c, 0) == 15
    assert evaluate(c, 1) == 54
    assert mult(a, b) == c
    assert divide(c, a)[0] == b
    assert divide(c, b)[0] == a

    a = parse('x^2 + 1')
    b = parse('x + 1')
    assert add(a, b) == parse('x^2 + x + 2')
    assert sub(a, b) == parse('x^2 + -x')
    c = parse('x^3 + x^2 + x + 1')
    assert evaluate(c, -1) == 0
    assert evaluate(c, 0) == 1
    assert evaluate(c, 1) == 4
    assert mult(a, b) == c
    assert divide(c, a)[0] == b
    assert divide(c, b)[0] == a

    a = parse('7x^3 + 5x^2 + 3x + 1')
    b = parse('19x^3 + 17x^2 + 13x + 11')
    assert add(a, b) == parse('26x^3 + 22x^2 + 16x + 12')
    assert sub(a, b) == parse('-12x^3 + -12x^2 + -10x + -10')
    c = parse('133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11')
    assert evaluate(c, -1) == 16
    assert evaluate(c, 0) == 11
    assert evaluate(c, 1) == 960
    assert mult(a, b) == c
    assert divide(c, a)[0] == b
    assert divide(c, b)[0] == a

    a = interpolate([(-1,2), (0,3), (1,6)])
    assert a == parse('x^2 + 2x + 3')

    breakpoint()
    a = interpolate([(1,1), (2,2), (3,3), (4,4), (5,5), (6,6)])
    print(a)
