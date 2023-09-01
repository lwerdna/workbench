#!/usr/bin/env python

import sys, re, math

from collections import defaultdict

import z3

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

# try to factor some target given degA and degB
def factor_deg(target, degA, degB):
    # generate the equations for a degree-A and degree-B product
    # basically a symbolic form of the mult() function
    variables = {}
    expressions = [0]*(degA + degB + 1)

    def get_var(name):
        if not name in variables:
            variables[name] = z3.Int(name)
        return variables[name]

    for da in range(degA+1):
        for db in range(degB+1):
            var_a = get_var(f'a_{da}')
            var_b = get_var(f'b_{db}')
            if expressions[da+db] == 0:
                expressions[da+db] = var_a * var_b
            else:
                expressions[da+db] += var_a * var_b
    
    assert len(expressions) == len(target)
    if 1:
        print(f'generated expressions for a {degA}-degree x {degB}-degree:')
        for expr in expressions:
            print(expr)

    equations = []
    for i in range(len(expressions)):
        equations.append(expressions[i] == target[i])
    if 1:
        print('generated equations:')
        for equ in equations:
            print(equ)

    s = z3.Solver()
    for k in equations:
        s.add(k)

    if s.check() == z3.sat:
        if 1:
            print('solutions:')
        a, b = [0]*(degA+1), [0]*(degB+1)
        m = s.model()
        lookup = {}
        for d in m.decls():
            assert m[d].is_int()
            letter, number = re.match(r'(.)_(.*)', d.name()).group(1,2)
            number = int(number)
            if letter == 'a':
                a[number] = m[d].as_long()
            elif letter == 'b':
                b[number] = m[d].as_long()

            if 1:
                print ("%s = %s" % (d.name(), m[d]))

        return a, b
    else:
        return None, None

def factor(poly):
    deg = degree(poly)

    for dA in range(1, degree(poly)//2+1):
        dB = deg - dA

        A, B = factor_deg(poly, dA, dB)

        if A and B:
            return A, B

    return None, None

if __name__ == '__main__':
    if sys.argv[1:]:
        c = parse(sys.argv[1])
        a, b = factor(c)
        if (a, b) == (None, None):
            print('prime')
        else:
            print('(' + unparse(a) + ')(' + unparse(b) + ')')
        
    else:
        print('TEST MODE!')
        a = parse('x^2 + 2x + 3')
        b = parse('4x + 5')
        print(mult(a, b))
        print(parse('4x^3 + 13x^2 + 22x + 15'))
        assert mult(a, b) == parse('4x^3 + 13x^2 + 22x + 15')

        a = parse('x^2 + 1')
        b = parse('x + 1')
        assert mult(a, b) == parse('x^3 + x^2 + x + 1')

        print('factor x^2 - 1')
        c = parse('x^2 + -1')
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        print(mult(a, b))
        assert mult(a, b) == c

        print('factor x^3 + x^2 + x + 1')
        a, b = factor([1, 1, 1, 1])
        print(f'a = {a}')
        print(f'b = {b}')

        print('factor 7x^3 + 5x^2 + 3x + 1')
        a, b = factor([1, 3, 5, 7])
        print(f'a = {a}')
        print(f'b = {b}')

        print('factor 19x^3 + 17x^2 + 13x + 11')
        a, b = factor([11, 13, 17, 19])
        print(f'a = {a}')
        print(f'b = {b}')

        print('multiply (7x^3 + 5x^2 + 3x + 1)(19x^3 + 17x^2 + 13x + 11)')
        print(mult([1, 3, 5, 7], [11, 13, 17, 19]))

        print('factor 133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11')
        a, b = factor([11, 46, 111, 212, 233, 214, 133])
        print(f'a = {a}')
        print(f'b = {b}')
