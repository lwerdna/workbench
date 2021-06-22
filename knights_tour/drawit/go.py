#!/usr/bin/env python

def moves(x, y):
    candidates = [ (x+1,y-2), (x+2,y-1), (x+1,y+2), (x+2,y+1),
                   (x-1,y-2), (x-2,y-1), (x-1,y+2), (x-2,y+1) ]
    return [c for c in candidates if c[0]>=0 and c[0]<8 and c[1]>=0 and c[1]<8]
    
def sqr2str(x, y):
    return 'abcdefgh'[x] + str(y+1)

print('digraph graphname {')
for (x,y) in [(a,b) for a in range(8) for b in range(8)]:
    for (x2,y2) in moves(x, y):
        print('\t%s -> %s;' % (sqr2str(x,y), sqr2str(x2,y2)))
print('}')

