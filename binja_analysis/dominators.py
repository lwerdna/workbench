#!/usr/bin/env python

import os, sys, re

import fizzbuzz
from helpers import *

func = bytes_to_function(fizzbuzz.binary)
print_function_disasm(func)

for src in func.basic_blocks:
    reds = [src]
    # note: a bb technically dominates itself, so a strict dominator excludes this case
    greens = [x for x in func.basic_blocks if x in src.strict_dominators]
    fname = 'dominators_%s' % bbname(src)
    graph_func(fname, func, reds, greens)

