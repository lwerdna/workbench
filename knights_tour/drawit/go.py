#!/usr/bin/env python

import itertools

def moves(square):
    (x,y) = square
    candidates = [ (x+1,y-2), (x+2,y-1), (x+1,y+2), (x+2,y+1),
                   (x-1,y-2), (x-2,y-1), (x-1,y+2), (x-2,y+1) ]
    return [c for c in candidates if c[0]>=0 and c[0]<8 and c[1]>=0 and c[1]<8]
    
def sqr2str(square):
    return 'abcdefgh'[square[0]] + str(square[1]+1)

print('digraph graphname {')
for src in [(x,y) for x in range(8) for y in range(8)]:
    for dst in moves(src):
        print('\t%s -> %s;' % (sqr2str(src), sqr2str(dst)))
print('}')

