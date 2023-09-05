#!/usr/bin/env python

import sys, re, math

import itertools

from helpers import *

# factor poly assuming a factor of degree d
def factor(poly, d):
    intercepts = []
    inputs = list(range(d+1)) # we need d+1 points to determine a degree-d polynomial

    for i in inputs:
        output = poly.evaluate(i)
        assert output.denominator == 1
        output = output.numerator
        print(f'c({i}) = {output}')

        divs = divisors(output)
        print(f'so a degree-{d} divisor a({i}) must be in {divs}')

        intercepts.append([(i, d) for d in divs])

    total = 1
    for group in intercepts:
        total *= len(group)
    #print(f'total product of points: {total}')

    #print(intercepts)

    for points in itertools.product(*intercepts):
        #print(f'interpolating {points}')
        
        a = interpolate(points)
        #print(a)

        if a.degree() == d:
            q, r = poly / a
            if r == 0:
                print('factor found! {a}')
                sys.exit(0)

    #print(intercepts)

if __name__ == '__main__':
    c = Polynomial('133x^6 + 214x^5 + 233x^4 + 212x^3 + 111x^2 + 46x + 11')
    factor(c, 3)
