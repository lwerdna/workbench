#!/usr/bin/env python

import sys
import binaryninja

def topo_order(func):
    result = []

    iedges = [0]*len(func.basic_blocks)
    for b in func.basic_blocks:
        iedges[b.index] = len([e for e in b.incoming_edges if not e.back_edge])

    stack = [func.basic_blocks[0]]
    while stack:
        block = stack.pop()
        result.append(block.index)

        for child in reversed([e.target for e in block.outgoing_edges]):
            iedges[child.index] -= 1
            if iedges[child.index] == 0:
                stack.append(child)

    return result

if __name__ == '__main__':
    fpath = sys.argv[1]
    bview = binaryninja.open_view(fpath)

    if sys.argv[2:]:
        fname = sys.argv[2]
        funcs = bview.get_functions_by_name(fname)
    else:
        funcs = list(bview.functions)

    for func in funcs:
        print(f'ordering blocks of {func}')
        result = topo_order(func)
        print(result)
