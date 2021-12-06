#!/usr/bin/env python

# dataset from https://users.cs.jmu.edu/adamses/Web/CS%20430%20Fall%202004/Code%20Examples/My%20Prolog%20Examples/family.htm
#
# weird, fay has 3 parents - shows the algorithm is SINGLE-INHERITANCE - insertion attempts stop after the first success

import sys
import random
import algorithm

parent_relationship = set([
    ('charles1', 'james1'),
    ('elizabeth', 'james1'),
    ('charles2', 'charles1'),
    ('catherine', 'charles1'),
    ('james2', 'charles1'),
    ('sophia', 'elizabeth'),
    ('george1', 'sophia'),
    ('george1', 'sam'),
    ('catherine', 'fay'),
    ('charles2', 'fay'),
    ('james2', 'fay'),
    ('sophia', 'paul'),
    ('elizabeth', 'claudia'),
    ('charles1', 'claudia')])

def ancestor(a, b):
    if (a, b) in parent_relationship:
        return True

    # a is not the parent of b
    # but is a the parent of x, and x is the ... parent of b?
    for (parent, child) in parent_relationship:
        if a==parent:
            if ancestor(child, b):
                return True

    return False

if __name__ == '__main__':
    # strings and substrings

    # doing this input list in any order should always produce the same hierarchy
    people = ['catherine', 'charles1', 'charles2', 'claudia', 'elizabeth', 'fay', 'george1',
    'james1', 'james2', 'paul', 'sam', 'sophia']

    result = algorithm.hierarchy(people, ancestor, lambda x:x)
    print(result)
