#!/usr/bin/env python

import sys

from helpers import *
from interpreter import *

if __name__ == '__main__':
    cases = []

    fpath = './test-cases.py'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    with open(fpath) as fp:
        lines = fp.readlines()

    starts = [i for i in range(len(lines)) if lines[i].startswith('# TEST:')]
    ends = starts[1:] + [len(lines)]
    assert len(starts) == len(ends)
    for (s,e) in zip(starts, ends):
        print('-'*80)
        print(lines[s].rstrip())
        print('-'*80)

        pycode_lines = lines[s+1: e]
        precond, postcond = parse_conditions(pycode_lines)
        print(f'precondition: {precond}')
        print(f'postcondition: {GREEN}{postcond}{NORMAL} (expected)')

        #
        tree = refine(parse(''.join(pycode_lines)), TreeNode)

        # run abstract interpretation
        postcond_actual = tree.AI(precond)

        print(f'  result postcondition: {RED}{postcond_actual}{NORMAL}')
        assert state_identical(postcond, postcond_actual)

        print('PASS')
