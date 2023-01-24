#!/usr/bin/env python

import os, sys, re, pprint

import multiset

class Quantity(object):
    def __init__(self, value, top, bottom):
        self.value = value
        self.top = top
        self.bottom = bottom

    def simplify(self):
        result = self.copy()
        while True:
            targets = [x for x in result.top if x in result.bottom]
            if not targets:
                break
            target = targets[0]
            result.top.remove(target)
            result.bottom.remove(target)
        return result

    def copy(self):
        return Quantity(self.value, list(self.top), list(self.bottom))

    def __mul__(self, other):
        result = Quantity(self.value * other.value, self.top + other.top, self.bottom + other.bottom)
        return result.simplify()

    def __add__(self, other):
        assert self.top == other.top
        assert self.bottom == other.bottom
        result = Quantity(self.value + other.value, list(self.top), list(self.bottom))
        return result.simplify()

    def __str__(self):
        def unique_elems(l):
            return list(set(l))

        result = f'{self.value} '
        result += '{'+','.join([f'{elem}^{self.top.count(elem)}' if self.top.count(elem)>1 else elem for elem in unique_elems(self.top)])+'}'
        if self.bottom:
            result += '/'
            result += '{'+','.join([f'{elem}^{self.bottom.count(elem)}' if self.bottom.count(elem)>1 else elem for elem in unique_elems(self.bottom)])+'}'

        return result

if __name__ == '__main__':
    print("Hello, world!")

    q = Quantity(128, ['ounce'], ['gallon'])
    assert str(q) == '128 {ounce}/{gallon}'

    # Example: convert 2.5 miles to inches
    result =    Quantity(2.5, ['mile'], []) * \
                Quantity(5280, ['foot'], ['mile']) * \
                Quantity(12, ['inch'], ['foot'])

    print(result)
    assert str(result) == '158400.0 {inch}'

    # Example: convert 65 miles per hour to feet per second
    result =    Quantity(65, ['mile'], ['hour']) * \
                Quantity(5280, ['foot'], ['mile']) * \
                Quantity(1/60, ['hour'], ['minute']) * \
                Quantity(1/60, ['minute'], ['second'])

    print(result)
    assert str(result) == '95.33333333333333 {foot}/{second}'

    # Example: convert 1km^2 to m^2
    assert str(Quantity(2.5, ['kilometer', 'kilometer'], [])) == '2.5 {kilometer^2}'

    result =    Quantity(1, ['kilometer', 'kilometer'], []) * \
                Quantity(1000, ['meter'], ['kilometer']) * \
                Quantity(1000, ['meter'], ['kilometer'])

    print(result)
    assert str(result) == '1000000 {meter^2}'
