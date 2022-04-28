#!/usr/bin/env python

# get ANGR to a state where you can play with symbols

import os, sys

import angr

fpath = '../testbins/tests-macos-x64-macho'
print('opening: ' + fpath)
proj = angr.Project(fpath)

state = proj.factory.entry_state()

solver = state.solver

one = solver.BVV(1, 64) # claripy.ast.bv.BV
one_hundred = solver.BVV(100, 64)
x = solver.BVS('x', 64) # claripy.ast.bv.BV (no indication of [S]ymbolic)
y = solver.BVS('y', 64)

solver.is_false(one == 1)
solver.is_false(one_hundred == 100)
solver.is_false(x == 1)

breakpoint()
