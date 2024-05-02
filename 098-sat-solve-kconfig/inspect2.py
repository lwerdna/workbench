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

    #all_syms = kconf.defined_syms

    #assert sys.argv[1:]
    #sym = next(s for s in all_syms if s.name == sys.argv[1])

    #print('starting debugger with "sym" assigned')
    breakpoint()

