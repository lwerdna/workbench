#!/usr/bin/env python

# test on sets, with relation(a,b) = a is a superset of b

import sys
import random
import algorithm

items = [
    set([1,2,3,4,5,6,7,8,9,10]),
    set([4,5]),
    set([6,7]),
    set([8]),
    set([3,4,5,6,7]),
    set([4,5,6]),
    set([7,8,9,10]),
    set([1,2]),
    set([9,10]),
    set([5]),
]

if __name__ == '__main__':
    ancestor_relation = lambda a,b: a > b
    root = algorithm.hierarchy(items, ancestor_relation)

    actual = str(root)
    print(actual)
    expected = 'root\n' + \
               '  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}\n' + \
               '    {3, 4, 5, 6, 7}\n' + \
               '      {6, 7}\n' + \
               '      {4, 5, 6}\n' + \
               '        {4, 5}\n' + \
               '          {5}\n' + \
               '    {8, 9, 10, 7}\n' + \
               '      {8}\n' + \
               '      {9, 10}\n' + \
               '    {1, 2}'
    assert(actual == expected)
    print('OK')
