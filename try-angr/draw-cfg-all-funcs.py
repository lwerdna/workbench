#!/usr/bin/env python

import os
import re
import sys

import angr

from pprint import pprint

from helpers import *

fpath = '../testbins/tests-macos-x64-macho'
if sys.argv[1:]:
    fpath = sys.argv[1]

project = angr.Project(fpath, load_options={"auto_load_libs": False})

# get Mach-O symbols
loader = project.loader
obj = loader.main_object
func_addrs = []
for s in obj.symbols:
    if s.is_import or s.linked_addr == 0:
        continue

    # not possible for Mach-O symbols
    #if not s.is_function:
    #    continue
    # so instead:
    if not re.match(r'^_[a-zA-Z].*', s.name):
        continue

    print(f'adding {s.name} addr 0x{s.linked_addr:X} to analysis queue')
    func_addrs.append(s.linked_addr)

cfg = project.analyses.CFGEmulated(keep_state=True, 
                             state_add_options=angr.sim_options.refs, 
                             starts = func_addrs,
                             context_sensitivity_level=2
                            )

lookup = {s.linked_addr : s.name for s in obj.symbols}
DrawGraphEnodes(cfg.graph, lookup, './cfg.png')
