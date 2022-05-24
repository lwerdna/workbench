#!/usr/bin/env python

# converts graphviz plaintext format (actually: a small subset of it) to SVG
# meant for sanity checks, testing
#
# usage:
# $ dot -y -Tplain /tmp/tmp.dot | ./plain2svg.py
#
# use 'arrowhead="none"' to ensure the final point in the edge statements is positioned
# at the start of the destination block's rectangle, eg:
#
# digraph G {
#   edge [arrowhead="none"]
#   ...

import os
import sys
import re

GRAPHVIZ_DPI = 96

RECT_ATTRIBS = 'stroke="black" stroke-width="1" fill="none"'
PATH_ATTRIBS = 'stroke="red" stroke-width="1" fill="none"'
CIRCLE_ATTRIBS = 'stroke="red" stroke-width="1" fill="green"'

SVG_HEADER = '''
<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="%f" height="%f">
  <defs>
    <marker id="arrow-TrueBranch" class="arrow TrueBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
      <path d="M 0 0 L 10 5 L 0 10 z" />
    </marker>
    <marker id="arrow-FalseBranch" class="arrow FalseBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
      <path d="M 0 0 L 10 5 L 0 10 z" />
    </marker>
    <marker id="arrow-UnconditionalBranch" class="arrow UnconditionalBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
      <path d="M 0 0 L 10 5 L 0 10 z" />
    </marker>
    <marker id="arrow-IndirectBranch" class="arrow IndirectBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
      <path d="M 0 0 L 10 5 L 0 10 z" />
    </marker>
  </defs>
'''

SVG_FOOTER = '''
</svg>
'''

# 'edge bb0 bb2 4 4.5002 2.0279 4.6544 2.2244 4.7976 2.4068 4.8921 2.5273 FalseBranch 1.6389 2.5764 solid black'
# ->
# { 'points' : [(4.5002, 2.0279), (4.6544, 2.2244), (4.7976, 2.4068), (4.8921, 2.5273)],
#   'label': 'FalseBranch',
#   'source': 'bb0',
#   'dest': 'bb2'
# }
def edgetxt_parse(line):
    toks = line.split(' ')
    assert toks[0] == 'edge'
    assert re.match(r'^bb\d+$', toks[1])
    assert re.match(r'^bb\d+$', toks[2])
    assert re.match(r'^\d+$', toks[3])
    num_points = int(toks[3])
    values = [float(s) for s in toks[4:4+2*num_points]]
    points = [(values[i], values[i+1]) for i in range(0, len(values), 2)]

    label = toks[4+2*num_points]

    return {'points':points, 'label':label, 'source':toks[1], 'dest':toks[2]}

# turn graphviz plaintext edge statement to a path
#
# - The first and last coordinates do not appear to be control points like the docs say:
#   https://graphviz.org/docs/outputs/plain/. They act as start and end points.
#
# example input:
#     'edge bb0 bb2 4 4.5002 2.0279 4.6544 2.2244 4.7976 2.4068 4.8921 2.5273 solid black' ->
# example output:
#     '<path d="M4.5002,2.0279 C4.6544,2.2244 4.7976,2.4068 4.8921,2.5273">'
def edgetxt_to_path(line, scale_factor=1):
    parsed = edgetxt_parse(line)
    cpoints = parsed['points']
    cpoints = [(x*scale_factor, y*scale_factor) for (x,y) in cpoints]
    cpoints = [(round(x,4), round(y,4)) for (x,y) in cpoints]
    result = f'<path class="edge {parsed["label"]}" d="'
    result += f'M{cpoints[0][0]},{cpoints[0][1]} '
    result += 'C' + ' '.join(['%s,%s'%p for p in cpoints[1:]])
    result += f'" {PATH_ATTRIBS} '
    result += f'marker-end="url(#arrow-{parsed["label"]})" '
    result += '/>'
    return [result]

# turn graphviz plaintext edge statement to dots marking the important points
#
# example input:
#     'edge bb0 bb2 4 4.5002 2.0279 4.6544 2.2244 4.7976 2.4068 4.8921 2.5273 solid black' ->
# example output:
#    ['<circle cx="4.5002" cy="2.0279" r=".05" stroke="red" stroke-width="0" fill="green" />'
#     '<circle cx="4.6544" cy="2.2244" r=".05" stroke="red" stroke-width="0" fill="green" />'
#     '<circle cx="4.7976" cy="2.4068" r=".05" stroke="red" stroke-width="0" fill="green" />'
#     '<circle cx="4.8921" cy="2.5273" r=".05" stroke="red" stroke-width="0" fill="green" />']
def edgetxt_to_dots(line, scale_factor=1):
    cpoints = edgetxt_parse(line)['points']
    cpoints = [(x*scale_factor, y*scale_factor) for (x,y) in cpoints]
    cpoints = [(round(x,4), round(y,4)) for (x,y) in cpoints]
    return [f'<circle cx="{p[0]}" cy="{p[1]}" r="2" {CIRCLE_ATTRIBS} />' for p in cpoints]

if __name__ == '__main__':

    lookup = {}
    for line in sys.stdin.readlines():
        line = line.strip()
        toks = line.split(' ')

        # eg: graph 1 2.8333 4.2222
        if toks[0] == 'graph':
            [w, h] = [round(float(x)*GRAPHVIZ_DPI + 4) for x in toks[2:4]]
            print(SVG_HEADER % (w, h))

        # eg: node bb0 5.7431 0.47222 4.3472 0.94444 bb0 solid rectangle black lightgrey
        elif toks[0] == 'node':
            bbidx = int(re.match(r'^bb(\d+)$', toks[1]).group(1))
            [x,y,w,h] = [float(x)*GRAPHVIZ_DPI for x in toks[2:2+4]]
            [x,y] = [x-w/2, y-h/2]
            [x,y,w,h] = [round(v,4) for v in [x,y,w,h]]
            print(f'    <rect x="{x}" y="{y}" width="{w}" height="{h}" {RECT_ATTRIBS} />')

        # eg: edge bb0 bb1 4 4.6726 0.94523 4.2681 1.1187 3.8202 1.3108 3.4653 1.4631 solid black
        elif toks[0] == 'edge':
            print(f'    <!-- generated from: {line} -->')
            for l in edgetxt_to_dots(line, GRAPHVIZ_DPI):
                print('    ' + l)
            for l in edgetxt_to_path(line, GRAPHVIZ_DPI):
                print('    ' + l)

    print(SVG_FOOTER)
