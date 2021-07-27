#!/usr/bin/env python

import os, sys, re

import fizzbuzz
from helpers import *

func = bytes_to_function(fizzbuzz.binary)
print_function_disasm(func)

# dominators: D dominates X when D is on every path start->...->X
for D in func.basic_blocks:
    reds = [D]
    # note: a bb technically dominates itself, so a strict dominator excludes this case
    greens = [X for X in func.basic_blocks if D in X.strict_dominators]
    fname = '%s_dominates' % bbname(D)
    graph_func(fname, func, reds, greens)

for X in func.basic_blocks:
    reds = [X]
    greens = [D for D in func.basic_blocks if D in X.strict_dominators]
    fname = '%s_dominated_by' % bbname(X)
    graph_func(fname, func, reds, greens)

# dominance frontier: D's frontier is the set of blocks where D's dominance stops
for D in func.basic_blocks:
    reds = [D]
    greens = [X for X in func.basic_blocks if D in X.strict_dominators]
    blues = [X for X in func.basic_blocks if X in D.dominance_frontier]
    fname = 'dominance_frontier_%s' % bbname(D)
    graph_func(fname, func, reds, greens, blues)

# post-dominators: D post-dominates X when D is on every the path X->...->end
for src in func.basic_blocks:
    reds = [src]
    greens = [x for x in func.basic_blocks if x in src.post_dominators]
    fname = 'post_dominators_%s' % bbname(src)
    graph_func(fname, func, reds, greens)
