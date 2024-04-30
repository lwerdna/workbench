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

    print('-----------------------')
    print(f'looking up: {sym_name}')
    print(f'     found: {repr(sym)}')

    select_map = helpers.create_select_map(kconf)
    print('-----------------------')
    print('selected by:')
    print('-----------------------')
    for symbol, condition in sorted(select_map[sym_name], key=lambda x: x[0].name):
        print(symbol.name + ' when ' + helpers.expr_to_str(condition))

    if sym.direct_dep:
        print('-----------------------')
        print('direct dependencies:')
        print('-----------------------')
        print(helpers.expr_to_str(sym.direct_dep))


    print('starting debugger with "sym" assigned')
    breakpoint()

