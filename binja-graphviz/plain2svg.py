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

from helpers import *

XY_SCALER = 96

if __name__ == '__main__':
    print(SVG_HEADER)

    lookup = {}
    for line in sys.stdin.readlines():
        line = line.strip()
        toks = line.split(' ')

        # eg: node bb0 5.7431 0.47222 4.3472 0.94444 bb0 solid rectangle black lightgrey
        if toks[0] == 'node':
            bbidx = int(re.match(r'^bb(\d+)$', toks[1]).group(1))
            [x,y,w,h] = [float(x)*XY_SCALER for x in toks[2:2+4]]
            [x,y] = [x-w/2, y-h/2]
            [x,y,w,h] = [round(v,4) for v in [x,y,w,h]]
            print(f'    <rect x="{x}" y="{y}" width="{w}" height="{h}" {RECT_ATTRIBS} />')

        # eg: edge bb0 bb1 4 4.6726 0.94523 4.2681 1.1187 3.8202 1.3108 3.4653 1.4631 solid black
        elif toks[0] == 'edge':
            print(f'    <!-- generated from: {line} -->')
            for l in edgetxt_to_dots(line, XY_SCALER):
                print('    ' + l)
            for l in edgetxt_to_path(line, XY_SCALER):
                print('    ' + l)

    print(SVG_FOOTER)
