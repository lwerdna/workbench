#!/usr/bin/env python

# convert a python model of an ITSA program to assembly

import ast
import os, sys, re
import random

from helpers import *

iter_probability = .7
or_probability = .5

label_i = 0
def generate_label():
    global label_i
    label_i += 1
    return f'.loc_{label_i:04d}'

def generate_labels():
    return (generate_label(), generate_label())

def gen_re(tree):
    if tree[0] == 'block':
        for stmt in tree[1:]:
            gen_re(stmt)
    elif tree[0] == 'init':
        for arg in reversed(tree[1:]):
            print(f'\tpush {arg}')
        print(f'\tcall init')
    elif tree[0] == 'translation':
        for arg in reversed(tree[1:]):
            print(f'\tpush {arg}')    
        print(f'\tcall translation')
    elif tree[0] == 'rotation':
        for arg in reversed(tree[1:]):
            print(f'\tpush {arg}')    
        print(f'\tcall rotation')
    elif tree[0] == 'iter':
        a, b = generate_labels()
        print(f'{a}:')
        print('\tcall unknown')
        print('\tcmp rax, 1')
        print(f'\tje {b}')
        gen_re(tree[1])
        print(f'\tjmp {a}')
        print(f'{b}:')

    elif tree[0] == 'or':
        a, b = generate_labels()
        print('\tcall unknown')
        print('\tcmp rax, 1')
        print(f'\tjne {a}')
        gen_re(tree[1])
        print(f'\tjmp {b}')
        print(f'{a}:')
        gen_re(tree[2])
        print(f'{b}:')

    else:
        breakpoint()

def gen(tree):
    print('default rel')
    print('global _main')
    print('section .text')
    print('')
    print('extern init')
    print('extern unknown')
    print('extern rotation')
    print('extern translation')
    print('')
    print('_main:')
    print('\tpush rbp')
    print('\tmov rbp, rsp')
    gen_re(tree)
    print('\tmov rax, 0')
    print('\tpop rbp')
    print('\tretn')

if __name__ == '__main__':
    with open(sys.argv[1], "r") as source:
        tree = refine(parse(source.read()))

    gen(tree)

