#!/usr/bin/env python

import time
import itertools

from z3 import *

# naive encoding with boolean variables
def solution0(n):
    clauses = []

    vdict = {}
    for row in range(n):
        for col in range(n):
            name = f'v_{row}_{col}'
            vdict[name] = z3.Bool(name)


    s = Solver()

    # verbose checks for attacks
    # v_0_0 -> Not(Or(v_0_1, v_0_2, v_0_3, ...
    for row in range(n):
        for col in range(n):
            pname = f'v_{row}_{col}'
            p = vdict[pname]

            # nothing on the same row or column
            qnames = [f'v_{r}_{c}' for (r, c) in itertools.product(range(n), range(n)) if \
                (r==row and c!=col) or (r!=row and c==col)]
            qs = [vdict[qname] for qname in qnames]

            #print('%s -> Not(Or(%s))' % (p, ', '.join([str(q) for q in qs])))
            s.add(Implies(p, Not(Or(*qs))))
   
    # verbose check for k variables being true
    # warning! generates nCr(n**2, n) clauses
    vset = set(vdict.values())
    disjuncts = []
    for ingroup in itertools.combinations(vset, n):
        disjuncts.append(z3.And(*list(ingroup)))
    s.add(Or(*disjuncts))

    return s

# this is solution 0, but uses z3's cardinality constraint
def solution1(n):
    vdict = {}
    for row in range(n):
        for col in range(n):
            name = f'v_{row}_{col}'
            vdict[name] = z3.Bool(name)

    s = Solver()

    # verbose checks for attacks
    # v_0_0 -> Not(Or(v_0_1, v_0_2, v_0_3, ...
    for row in range(n):
        for col in range(n):
            pname = f'v_{row}_{col}'
            p = vdict[pname]

            # nothing on the same row or column
            qnames = [f'v_{r}_{c}' for (r, c) in itertools.product(range(n), range(n)) if \
                (r==row and c!=col) or (r!=row and c==col)]
            qs = [vdict[qname] for qname in qnames]

            #print('%s -> Not(Or(%s))' % (p, ', '.join([str(q) for q in qs])))
            s.add(Implies(p, Not(Or(*qs))))

    # at least n rooks
    s.add(AtLeast(*(list(vdict.values()) + [n])))

    return s

# another boolean variables encoding, using cardinality constraints to enforce
# attack rules
# eg: "at most 1 rook on a row" covers "two rooks on the row can't attack each other"
def solution2(n):
    # varmat[x][y] contains variable "v_x_y"
    varmat = [[z3.Bool(f'v_{x}_{y}') for x in range(n)] for y in range(n)]

    s = Solver()

    # all rows can have at most 1 rook
    for row in varmat:
        s.add(AtMost(*(row + [1])))
    # all columns can have at most 1 rook
    for c in range(n):
        s.add(AtMost(*([varmat[r][c] for r in range(n)] + [1])))

    return s

if __name__ == '__main__':
    # width of board in squares
    width = 10

    s = solution0(width)
    print(s.sexpr())

    t0 = time.time()
    assert s.check() == z3.sat
    t1 = time.time()
    m = s.model()
    t2 = time.time()

    print('check():%fs model():%fs' % (t1-t0, t2-t1))

    def piece(b):
        return 'R' if b else '-'

    name2var = {v.name(): v for v in m.decls()}
    name2val = {name: m[var] for (name, var) in name2var.items()}
    name2char = {name: piece(val) for (name, val) in name2val.items()}


    for row in range(width):
        for col in range(width):
            name = f'v_{row}_{col}'
            print(name2char[name]+' ', end='')
        print()


