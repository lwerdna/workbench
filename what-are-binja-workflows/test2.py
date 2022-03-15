#!/usr/bin/env python

# insert an activity to execute immediately after lifted IL

import sys
import binaryninja
from binaryninja.workflow import Activity, Workflow

def action_func(analysis_context):
    print('Hello')

if __name__ == '__main__':
    fpath = sys.argv[1]

    wf = Workflow().clone('MyWorkflow')
    a = Activity('MyActivity', action=action_func)
    result = wf.register_activity(a)
    assert result == True

    # the topology as we expected?
    subactivities = wf.subactivities('core.function.basicAnalysis')
    assert subactivities[0] == 'core.function.generateLiftedIL'
    assert subactivities[1] == 'core.function.resetIndirectBranchesOnFullUpdate'

    # insert, finalize workflow
    result = wf.insert('core.function.resetIndirectBranchesOnFullUpdate', ['MyActivity'])
    assert result == True
    result = wf.register()
    assert result == True

    # did we change the topology as expected?
    subactivities = wf.subactivities('core.function.basicAnalysis')
    assert subactivities[0] == 'core.function.generateLiftedIL'
    assert subactivities[1] == 'MyActivity'
    assert subactivities[2] == 'core.function.resetIndirectBranchesOnFullUpdate'

    print('open_view()')

    bv = binaryninja.open_view(fpath, \
      options={'workflows.enable':True, 'workflows.functionWorkflow':'MyWorkflow'})

    print('done')  
