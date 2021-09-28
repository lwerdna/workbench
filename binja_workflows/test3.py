#!/usr/bin/env python

# generate code to hook every activity of workflows

import os, sys, re, pprint
import json

from binaryninja.workflow import Activity, Workflow

wf = Workflow()
json_text = wf.configuration()
jdict = json.loads(json_text)

seen = set()
for (src, dsts) in jdict.items():
    seen.add(src)
    for dst in dsts:
        seen.add(dst)

# generate the functions
for activity_name in seen:
    wfhook_func = 'hook_' + activity_name.replace('.', '_')

    print('extern "C" void %s(Ref<AnalysisContext> analysisContext)' % wfhook_func)
    print('{')
    print('\tRef<Function> function = analysisContext->GetFunction();')
    print('\tprintf("0x%%" PRIx64 " %s()\\n", function->GetStart());' % wfhook_func)
    print('')
    print('\tRef<LowLevelILFunction> llilFunc = analysisContext->GetLowLevelILFunction();')
    print('\tprintf("LLIL instruction count is: %zu\\n", llilFunc->GetInstructionCount());')
    print('}')
    print('')

# generate the code to register the functions
for activity_name in seen:
    # don't insert in front of the root
    if activity_name == 'core.function.defaultAnalysis':
        continue

    wfhook_name = 'extension.WFHook.' + activity_name
    wfhook_func = 'hook_' + activity_name.replace('.', '_')

    print('\twf->RegisterActivity(new Activity("%s", &%s));' % (wfhook_name, wfhook_func))
    print('\twf->Insert("%s", "%s");' % (activity_name, wfhook_name))
    print('')
