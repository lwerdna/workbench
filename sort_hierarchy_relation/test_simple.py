#!/usr/bin/env python

# test on the instruction class and instruction form names from the A64 specification

import sys
import random
import algorithm

if __name__ == '__main__':
    # strings and substrings

    # doing this input list in any order should always produce the same hierarchy
    ancestor_relation = lambda a,b: b.startswith(a)
    sort_key = lambda x: x
    items = ['aardvark', 'ant', 'antelope', 'anteater', 'a']
    for i in range(10):
        random.shuffle(items)
        print('input: items')
        result = algorithm.hierarchy(items, ancestor_relation, sort_key)
        actual = str(result)
        expected = 'root\n  a\n    aardvark\n    ant\n      anteater\n      antelope'
        print('output:\n' + actual)
        assert(actual == expected)
        print('OK')

