#!/usr/bin/env python

import os, sys
from pprint import pprint

import angr

from helpers import *

fpath = '../testbins/tests-macos-x64-macho'
if sys.argv[1:]:
    fpath = sys.argv[1]

sname = '_main'
if sys.argv[2:]:
    sname = sys.argv[2]

print(f'opening: {fpath}')
project = angr.Project(fpath, load_options={"auto_load_libs": False})

symbols = GetSymbolsByName(project, sname)
for s in symbols:
    print(s)
