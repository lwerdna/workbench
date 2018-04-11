#!/usr/bin/python

lens = []
for i in range(64):
    row = i/8;
    col = i%8;

    foo = []
#    foo.append([row-1, col+2])
#    foo.append([row+1, col+2])
#    foo.append([row+2, col+1])
#    foo.append([row+2, col-1])
#    foo.append([row-1, col-2])
#    foo.append([row+1, col-2])
#    foo.append([row-2, col-1])
#    foo.append([row-2, col+1])

    foo.append([row+2, col-1])
    foo.append([row+2, col+1])
    foo.append([row+1, col-2])
    foo.append([row+1, col+2])
    foo.append([row-1, col-2])
    foo.append([row-1, col+2])
    foo.append([row-2, col-1])
    foo.append([row-2, col+1])

    oks = []
    for sq in foo:
        if sq[0] > 7 or sq[0] < 0 or \
            sq[1] > 7 or sq[1] < 0:
            continue

        oks.append(sq[0]*8 + sq[1])
    
    lens.append(len(oks));

    while(len(oks) < 8):
        oks.append(-1)
    
    print "/* sq%d (%d,%d) */ " % (i, row, col),
    print '{', ','.join(map((lambda x: '%d' % x), oks)), '},'


print '{ ', ','.join(map((lambda x: str(x)), lens)), '};'



