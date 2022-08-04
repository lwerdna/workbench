#!/usr/bin/env python

import os
import sys
from pprint import pprint

import angr
import angr.calling_conventions
import claripy

from helpers import *

fpath = '../testbins/tests-macos-x64-macho'
if sys.argv[1:]:
    fpath = sys.argv[1]
project = angr.Project(fpath, load_options={"auto_load_libs": False})

# get start/end addresses
addr_start = GetFunctionAddress(project, '_print_2path')
addr_end = GetFunctionAddress(project, '_mark_success')
print(f'searching %08X -> %08X' % (addr_start, addr_end))

# .call_state()
arg1 = claripy.BVS('arg1', 32)
#state = project.factory.call_state(addr_start, arg1, cc=angr.calling_conventions.SimCCSystemVAMD64)
state = project.factory.call_state(addr_start, arg1)

sm = project.factory.simulation_manager(state)

print('explore()')
sm.explore(find=addr_end)
assert sm.found

state = sm.found[0]

breakpoint()

# print trace, METHOD#1
def history_addrs(history):
    if not history or not history.addr:
        return []
    return history_addrs(history.parent) + [history.addr]
trace = history_addrs(state.history) + [state.addr]
print(' -> '.join([hex(a) for a in trace]))

# print trace, METHOD#2
for state in sm.active:
    trace = list(state.history.bbl_addrs) + [state.addr]
    print(', '.join([hex(a) for a in trace]))

