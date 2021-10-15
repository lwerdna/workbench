#!/usr/bin/env python
# draw function with loop blocks in red

import os, sys, re
from helpers import *

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    fname = '_some_loops' if not sys.argv[2:] else sys.argv[2]
    (bv, func) = quick_get_func(fpath, fname)

    all_loop_blocks = []

    for (i,loop) in enumerate(calculate_natural_loops(func)):
        print('loop%d has blocks: %s' % (i, loop))
        graphviz_func('loop_%d' % i, func, loop, [])
        all_loop_blocks.extend(loop)

    graphviz_func('loop_all', func, all_loop_blocks, [])
