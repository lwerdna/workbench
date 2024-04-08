#!/usr/bin/env python

import os
import sys

import helpers
import kconfiglib

if __name__ == '__main__':
    tmp = sys.argv
    sys.argv = sys.argv[0:1]
    kconf = helpers.get_kconf_object()
    sys.argv = tmp

    assert sys.argv[1:]
    sym_name = sys.argv[1]

    if 0:
        # manual way
        all_syms = kconf.defined_syms
        sym = next(s for s in all_syms if s.name == sym_name)
    else:
        sym = kconf.syms[sym_name]

    select_map = helpers.create_select_map(kconf)
    print('selected by:')
    for selector in sorted(select_map[sym_name]):
        print('  ' + selector)

    print('starting debugger with "sym" assigned')
    breakpoint()

