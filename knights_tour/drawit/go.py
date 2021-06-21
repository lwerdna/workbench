#!/usr/bin/env python

import os, sys, re
import itertools

def moves(square):
    (x,y) = square
    candidates = [ (x+1,y-2), (x+2,y-1), (x+1,y+2), (x+2,y+1),
                   (x-1,y-2), (x-2,y-1), (x-1,y+2), (x-2,y+1) ]
    return [c for c in candidates if c[0]>0 and c[0]<9 and c[1]>0 and c[1]<9]
    
def sqr2str(square):
    return 'abcdefgh'[square[0]-1] + str(square[1])

squares = itertools.product([1,2,3,4,5,6,7,8], [1,2,3,4,5,6,7,8])

with open('tour.dot', 'w') as fp:
    fp.write('digraph graphname {\n')
    for src in squares:
        for dst in moves(src):
            fp.write('\t%s -> %s;\n' % (sqr2str(src), sqr2str(dst)))
    fp.write('}\n')

os.system('dot -Tsvg tour.dot -o tour.svg')
