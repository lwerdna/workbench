#!/usr/bin/env python

import re

# parse strings to [c0, c1, ..., c<degree>] representation, eg:
# "133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11" -> [11, 46, 111, 212, 233, 214, 133]
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

# return the degree of a polynomial in [c0, c1, ..., c<degree>] representation
def degree(poly):
    return len(poly)-1

# multiply two polynomials in [c0, c1, ..., c<degree>] representation
def mult(poly_a, poly_b):
    result = [0]*(degree(poly_a) + degree(poly_b) + 1)

    for (degA, cA) in enumerate(poly_a):      
        for (degB, cB) in enumerate(poly_b):
            result[degA + degB] += cA * cB

    return result

if __name__ == '__main__':
    print('TEST MODE!')
    a = parse('x^2 + 2x + 3')
    b = parse('4x + 5')
    assert mult(a, b) == parse('4x^3 + 13x^2 + 22x + 15')

    a = parse('x^2 + 1')
    b = parse('x + 1')
    assert mult(a, b) == parse('x^3 + x^2 + x + 1')

    print('multiply (7x^3 + 5x^2 + 3x + 1)(19x^3 + 17x^2 + 13x + 11)')
    print(mult([1, 3, 5, 7], [11, 13, 17, 19]))


