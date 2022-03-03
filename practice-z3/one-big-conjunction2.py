#!/usr/bin/env python

# Is one big conjunction the same as a bunch of solver.add()'s ?

# despite what stackoverflow says, the individual asserts solve much faster (.5 seconds vs. 8 seconds)
# however, dumping the smt2 and calling solve on those takes the same time

# https://stackoverflow.com/questions/28036350/z3-performance-many-assertions-vs-large-conjunction
# https://stackoverflow.com/questions/24711329/which-is-better-practice-in-smt-to-add-multiple-assertions-or-single-and/24712801#24712801

import time
import itertools

from z3 import *

# naive encoding with boolean variables
def get_n_rooks_solver(n, one_big_conjunction=False):
    assert n <= 5 # otherwise nCr(n*n, n) is too large

    clauses = []

    vdict = {}
    for row in range(n):
        for col in range(n):
            name = f'v_{row}_{col}'
            vdict[name] = z3.Bool(name)

    s = Solver()
    print('get_n_rooks_solver() id(s)=%d' % id(s))

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
            if one_big_conjunction:
                clauses.append(Implies(p, Not(Or(*qs))))
            else:
                s.add(Implies(p, Not(Or(*qs))))

    # verbose check for k variables being true
    # warning! generates nCr(n**2, n) clauses
    vset = set(vdict.values())
    disjuncts = []
    for ingroup in itertools.combinations(vset, n):
        disjuncts.append(z3.And(*list(ingroup)))
    if one_big_conjunction:
        clauses.append(Or(*disjuncts))
    else:
        s.add(Or(*disjuncts))

    if one_big_conjunction:
        #for c in clauses:
        #    s.add(c)
        s.add(And(*clauses))

    return s

def print_solution(m):
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

def dump_smt_lib(solver, fpath):
    with open(fpath, 'w') as fp:
        fp.write(solver.sexpr())
        fp.write('\n(check-sat)\n(get-model)\n')

if __name__ == '__main__':
    # width of board in squares
    width = 5

    s = get_n_rooks_solver(width, False)
    print('get_n_rooks_solver(width, False) returns id(s)=%d' % id(s))
    dump_smt_lib(s, '/tmp/a.smt2')
    t0 = time.time()
    s.check()
    with open('/tmp/a.stats', 'w') as fp:
        fp.write(str(s.statistics()))
    print('solution via adding clauses to the solver took %fs' % (time.time() - t0))
    print_solution(s.model())
    del s

    s2 = get_n_rooks_solver(width, True)
    print('get_n_rooks_solver(width, True) returns id(s)=%d' % id(s2))
    dump_smt_lib(s2, '/tmp/b.smt2')
    t0 = time.time()
    #assert s.check() == z3.sat
    s2.check()
    with open('/tmp/b.stats', 'w') as fp:
        fp.write(str(s2.statistics()))
    print('solution via one big conjunction took %fs' % (time.time() - t0))
    print_solution(s2.model())
    del s2

    s3 = get_n_rooks_solver(width, True)
    print('get_n_rooks_solver(width, True) returns id(s)=%d' % id(s3))
    dump_smt_lib(s3, '/tmp/c.smt2')
    t0 = time.time()
    #assert s.check() == z3.sat
    s3.check()
    with open('/tmp/c.stats', 'w') as fp:
        fp.write(str(s3.statistics()))
    print('solution via one big conjunction took %fs' % (time.time() - t0))
    print_solution(s3.model())
    del s3

    s4 = get_n_rooks_solver(width, True)
    print('get_n_rooks_solver(width, True) returns id(s)=%d' % id(s4))
    dump_smt_lib(s4, '/tmp/d.smt2')
    t0 = time.time()
    s4.check()
    with open('/tmp/d.stats', 'w') as fp:
        fp.write(str(s4.statistics()))
    print('solution via one big conjunction took %fs' % (time.time() - t0))
    print_solution(s4.model())
    del s4

