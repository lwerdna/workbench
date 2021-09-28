#!/usr/bin/env python

# this exercises the full hook workflow

import os, sys

import binaryninja
from binaryninja.binaryview import BinaryViewType

fpath = os.path.join(os.environ['HOME'], 'fdumps', 'filesamples', 'hello-macos-x64.macho')
if sys.argv[1:]:
    fpath = sys.argv[1]

print('get_view_of_file("%s")' % fpath)
#bv = BinaryViewType.get_view_of_file(fpath)
bv = binaryninja.open_view(fpath, \
  options={'workflows.enable':True, 'workflows.functionWorkflow':'WFHookWorkflow'})

print('update_analysis_and_wait()')
bv.update_analysis_and_wait()

print('iterating over functions')
for func in bv.functions:
    print(func)
