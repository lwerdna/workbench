#!/usr/bin/env python

import sys, re, math

from collections import defaultdict

import z3

from helpers import *

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

        expr = 'x^2 + -1'
        print(f'factor {expr}')
        c = parse(expr)
        assert c == [-1, 0, 1]
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        print(mult(a, b))
        assert mult(a, b) == c

        expr = 'x^3 + x^2 + x + 1'
        print(f'factor {expr}')
        c = parse(expr)
        assert c == [1, 1, 1, 1]
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        print(mult(a, b))
        assert mult(a, b) == c

        expr = '7x^3 + 5x^2 + 3x + 1'
        print(f'factor {expr}')
        c = parse(expr)
        assert c == [1, 3, 5, 7]
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        if a or b:
            print(mult(a, b))
            assert mult(a, b) == c

        expr = '19x^3 + 17x^2 + 13x + 11'
        print(f'factor {expr}')
        c = parse(expr)
        assert c == [11, 13, 17, 19]
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        if a or b:
            print(mult(a, b))
            assert mult(a, b) == c

        expr = '133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11'
        print(f'factor {expr}')
        c = parse(expr)
        a, b = factor(c)
        print(f'a = {a}')
        print(f'b = {b}')
        if a or b:
            print(mult(a, b))
            assert mult(a, b) == c        
