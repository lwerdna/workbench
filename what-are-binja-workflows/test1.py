#!/usr/bin/env python

# draw the default workflow "behavior tree" in graphviz

import os, sys, re, pprint
import json

from binaryninja.workflow import Activity, Workflow

def draw_digraph(edges):
    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\trankdir=LR;\n')
        for (a,b) in edges:
            fp.write('\t%s -> %s\n' % (a,b))
        fp.write('}\n')
    os.system('dot /tmp/tmp.dot -Tpng -o /tmp/tmp.png')

wf = Workflow()
json_text = wf.configuration()
jdict = json.loads(json_text)

edges = []
for (src,dsts) in jdict.items():
    # eg:
    # 'core.function.commitAnalysisData': []
    if not dsts: continue

    # eg:
    # 'core.function.defaultAnalysis': ['core.function.update']
    for dst in dsts:
        edges.append((src, dst))

edges = [(x[0].replace('.', '_'), x[1].replace('.', '_')) for x in edges]
#edges = [(x[0].replace('core.function.', ''), x[1].replace('core.function.', '')) for x in edges]

draw_digraph(edges)
