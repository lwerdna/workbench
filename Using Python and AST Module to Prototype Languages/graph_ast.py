#!/usr/bin/env python

import ast
import os, sys, re
import random

from helpers import *

class Cfg:
    def __init__(self):
        pass

vert_i = 0
def gen_vert_id():
    global vert_i
    result = f'vert{vert_i}'
    vert_i += 1
    return result

seen = {}

def make_cfg_re(tree):
    result = []

    global iter_probability, or_probability

    if tree[0] == 'block':
        for v in tree[1:]:
            make_cfg_re(v)
        for i in range(len(tree[1:-1])):
            print(f'{id(tree[i])} -> {id(tree[i+1])}')
    elif tree[0] == 'init':
        label = 'init(' + ','.join([str(k) for k in tree[1:]]) + ')'
        print(f'{id(tree[i])} [label="{label}"]')
    elif tree[0] == 'translation':
        label = 'translation(' + ','.join([str(k) for k in tree[1:]]) + ')'
        print(f'{id(tree[i])} [label="{label}"]')
    elif tree[0] == 'rotation':
        label = 'rotation(' + ','.join([str(k) for k in tree[1:]]) + ')'
        print(f'{id(tree[i])} [label="{label}"]')
    elif tree[0] == 'iter':
        print(f'{id(tree[i])} [label="iter"]')
        breakpoint()
        #make_cfg_re(tree[
    elif tree[0] == 'or':
        breakpoint()
    else:
        breakpoint()

def make_cfg(tree):
    start = gen_vert_id()
    end = gen_vert_id()

    make_cfg_re(tree)

if __name__ == '__main__':
    with open(sys.argv[1], "r") as source:
        tree = refine(parse(source.read()))

    make_cfg(tree)

