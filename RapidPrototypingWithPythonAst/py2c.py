#!/usr/bin/env python

# convert a python model of an ITSA program to C

import ast
import os, sys, re
import random

from helpers import *

iter_probability = .7
or_probability = .5

def gen_re(tree, depth=0):
    indent = '\t'*depth

    if tree[0] == 'block':
        for stmt in tree[1:]:
            gen_re(stmt, depth)
    elif tree[0] == 'init':
        argstr = ', '.join([str(x) for x in tree[1:]])
        print(f'{indent}init({argstr});')
    elif tree[0] == 'translation':
        argstr = ', '.join([str(x) for x in tree[1:]])
        print(f'{indent}translation({argstr});')
    elif tree[0] == 'rotation':
        argstr = ', '.join([str(x) for x in tree[1:]])
        print(f'{indent}rotation({argstr});')
    elif tree[0] == 'iter':
        print(f'{indent}while(unknown())')
        print(f'{indent}{{')
        gen_re(tree[1], depth+1)
        print(f'{indent}}}')

    elif tree[0] == 'or':
        print(f'{indent}if(unknown())')
        print(f'{indent}{{')
        gen_re(tree[1], depth+1)
        print(f'{indent}}}')
        print(f'{indent}else')
        print(f'{indent}{{')
        gen_re(tree[2], depth+1)
        print(f'{indent}}}')

    else:
        breakpoint()

def gen(tree):
    print('extern void init();')
    print('extern void rotation();')
    print('extern void translation();')
    print('extern int unknown();')
    print('')
    print('void function(void)')
    print('{')
    gen_re(tree, 1)
    print('\treturn;')
    print('}')

if __name__ == '__main__':
    with open(sys.argv[1], "r") as source:
        tree = refine(parse(source.read()))

    gen(tree)

