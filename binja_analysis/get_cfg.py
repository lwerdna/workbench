#!/usr/bin/env python

import os, sys, re

import fizzbuzz
from helpers import *

func = bytes_to_function(fizzbuzz.binary)
print_function_disasm(func)

# create graph
dot = []
dot.append('digraph G {')
for src in func.basic_blocks:
    for edge in src.outgoing_edges:
        dst = edge.target
        # basic block labels are "b" followed by index in containing function's
        # basic_blocks list
        dot.append('b%d -> b%d' % (src.index, dst.index))
dot.append('}')

with open('cfg.dot', 'w') as fp:
    fp.write('\n'.join(dot))

os.system('dot ./cfg.dot -Tpng -o cfg_dot.png')
#os.system('neato ./cfg.dot -Tpng -o cfg_neato.png')
#os.system('fdp ./cfg.dot -Tpng -o cfg_fdp.png')
#os.system('sfdp ./cfg.dot -Tpng -o cfg_sfdp.png')
#os.system('twopi ./cfg.dot -Tpng -o cfg_twopi.png')
#os.system('circo ./cfg.dot -Tpng -o cfg_circo.png')
