#!/usr/bin/env python3
# does Zain's new .in_loop attribute of BasicBlock work?

import sys
import binaryninja

fpath = (sys.argv[1:] and sys.argv[1]) or './tests'
symname = (sys.argv[2:] and sys.argv[2]) or '_some_loops'
bv = binaryninja.open_view(fpath, True, None, {'analysis.mode':'controlFlow'})

func = next((f for f in bv.functions if f.name == symname), None)
if not func:
    print('function %s not found, available are:' % symname)
    print(', '.join([f.name for f in bv.functions]))
    sys.exit(-1)

print('-------- analyzing function %s --------' % func.name)
for (i,bb) in enumerate(func.basic_blocks):
    print('b%d: %s.in_loop = %s' % (i, bb, bb.in_loop))
