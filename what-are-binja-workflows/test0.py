#!/usr/bin/env python

# register a workflow and open a file with it

import os, sys, re, pprint

import binaryninja
from binaryninja.workflow import Activity, Workflow

def action_func(analysis_context):
    # analysis_context is a: binaryninja._binaryninjacore.LP_BNAnalysisContext
    # and currently has no python exposed methods
    breakpoint()
    print('Hello')

if __name__ == '__main__':
    fpath = os.path.join(os.environ['HOME'], 'fdumps', 'filesamples', 'tests')
    if len(sys.argv) > 1:
        fpath = sys.argv[1]

    wf = Workflow().clone('MyWorkflow')
    a = Activity('MyActivity', action=action_func)
    result = wf.register_activity(a)
    assert result == True
    result = wf.insert('core.function.basicBlockAnalysis', ['MyActivity'])
    assert result == True
    result = wf.register()
    assert result == True

    print('open_view(%s)' % fpath)

    bv = binaryninja.open_view(fpath, \
      options={'workflows.enable':True, 'workflows.functionWorkflow':'MyWorkflow'})

    print('done')  
