#!/usr/bin/env python

# Is one big conjunction the same as a bunch of solver.add()'s ?

# despite what stackoverflow says, the individual asserts solve much faster
# however, dumping the smt2 and calling solve on those takes the same time, wtf?

# https://stackoverflow.com/questions/28036350/z3-performance-many-assertions-vs-large-conjunction
# https://stackoverflow.com/questions/24711329/which-is-better-practice-in-smt-to-add-multiple-assertions-or-single-and/24712801#24712801

import time
import cProfile
import itertools

from z3 import *

# naive encoding with boolean variables
def get_n_rooks_solver_A():
    n = 5

    vdict = {}
    for row in range(n):
        for col in range(n):
            name = f'v_{row}_{col}'
            vdict[name] = z3.Bool(name)

    s = Solver(logFile='/tmp/a.log')

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

def get_n_rooks_solver_B():
    n = 5

    clauses = []

    vdict = {}
    for row in range(n):
        for col in range(n):
            name = f'v_{row}_{col}'
            vdict[name] = z3.Bool(name)

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
            clauses.append(Implies(p, Not(Or(*qs))))

    # verbose check for k variables being true
    # warning! generates nCr(n**2, n) clauses
    vset = set(vdict.values())
    disjuncts = []
    for ingroup in itertools.combinations(vset, n):
        disjuncts.append(z3.And(*list(ingroup)))
    clauses.append(Or(*disjuncts))

    s2 = Solver(logFile='/tmp/b.log')
    s2.add(And(*clauses))
    return s2

def print_solution(m):
    name2var = {v.name(): v for v in m.decls()}
    name2val = {name: m[var] for (name, var) in name2var.items()}
    name2char = {name: ('R' if val else '-') for (name, val) in name2val.items()}

    for row in range(5):
        for col in range(5):
            name = f'v_{row}_{col}'
            print(name2char[name]+' ', end='')
        print()

def dump_smt_lib(solver, fpath):
    with open(fpath, 'w') as fp:
        fp.write(s.sexpr())
        fp.write('\n(check-sat)\n(get-model)\n')

if __name__ == '__main__':
    t0 = time.time()
    s = get_n_rooks_solver_A()
    with open('/tmp/a.assertions', 'w') as fp:
        for c in s.assertions():
            fp.write(str(c) + '\n')
    print('get_n_rooks_solver_A(): took %fs' % (time.time() - t0))
    dump_smt_lib(s, '/tmp/a.smt2')
    t0 = time.time()
    cProfile.run('s.check()')
    print("elapsed: %fs" % (time.time() - t0))
    #assert s.check() == z3.sat
    with open('/tmp/a.stats', 'w') as fp:
        fp.write(str(s.statistics()))    
    print('solution via adding clauses to the solver took %fs' % (time.time() - t0))
    print_solution(s.model())

    #s.reset()
    #del s

    t0 = time.time()

    #s2 = get_n_rooks_solver_B()
    s2 = Solver()
    s2.add(z3.And(s.assertions()))

    with open('/tmp/b.assertions', 'w') as fp:
        for c in s2.assertions():
            fp.write(str(c) + '\n')
    print('get_n_rooks_solver_B(): took %fs' % (time.time() - t0))
    dump_smt_lib(s2, '/tmp/b.smt2')
    t0 = time.time()
    cProfile.run('s2.check()')
    print("elapsed: %fs" % (time.time() - t0))
    #assert s2.check() == z3.sat
    with open('/tmp/b.stats', 'w') as fp:
        fp.write(str(s2.statistics()))    
    print('solution via one big conjunction took %fs' % (time.time() - t0))
    print_solution(s2.model())
