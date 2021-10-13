#!/usr/bin/env python

import sys
from helpers import *
from loops import get_loops

if __name__ == '__main__':
    fpath = './tests' if not sys.argv[1:] else sys.argv[1]
    func = None if not sys.argv[2:] else sys.argv[2]

    (bv, func) = quick_get_func(fpath, None)
    if not bv:
        raise Exception('binary ninja didnt return analysis on -%s-' % fpath)

    functions = [func] if func else bv.functions
    for func in functions:
        print('-------- analyzing function %s --------' % func.name)

        depths = calculate_depths(func)

        for bb in func.basic_blocks:
            for edge in bb.outgoing_edges:
                (header, footer) = (edge.target, edge.source)

                oracle = depths[bbid(header)] < depths[bbid(footer)]

                if edge.back_edge != oracle:
                    print('%s address=%08X depth=%d' % (bbid(footer), footer.start, depths[bbid(footer)]))
                    print('%s address=%08X depth=%d' % (bbid(header), header.start, depths[bbid(header)]))
                    raise Exception('is edge %s -> %s a non-strict back edge? binja:%s oracle:%s' %
                        (bbid(footer), bbid(header), edge.back_edge, oracle))

