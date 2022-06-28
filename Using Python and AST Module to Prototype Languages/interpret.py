#!/usr/bin/env python

# interpret/execute a python model of an ITSA program

import ast
import os, sys, re
import random

from helpers import *

iter_probability = .7
or_probability = .5

def execute(tree):
    global iter_probability, or_probability

    if tree[0] == 'block':
        for stmt in tree[1:]:
            execute(stmt)
    elif tree[0] == 'init':
        print(f'init({tree[1:]})')
    elif tree[0] == 'translation':
        print(f'translation({tree[1:]})')
    elif tree[0] == 'rotation':
        print(f'rotation({tree[1:]})')
    elif tree[0] == 'iter':
        while True:
            taken = random.random() < iter_probability
            print(f'iteration taken? {taken}')
            if not taken: break
            execute(tree[1])
    elif tree[0] == 'or':
        taken = random.random() < or_probability
        print(f'or taken? {taken}')
        if taken:
            execute(tree[1])
        else:
            execute(tree[2])
    else:
        breakpoint()

if __name__ == '__main__':
    with open(sys.argv[1], "r") as source:
        tree = refine(parse(source.read()))

    print('-------- EXECUTED AST --------')
    execute(tree)

