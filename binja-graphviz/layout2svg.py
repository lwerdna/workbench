#!/usr/bin/env python

import os
import sys
import re
import json
from helpers import *

if __name__ == '__main__':
    print(SVG_HEADER)

    data = None
    with open(sys.argv[1]) as fp:
        data = json.loads(fp.read())

    for block in data['blocks']:
        [x,y,w,h] = block['rect']
        print(f'    <rect x="{x}" y="{y}" width="{w}" height="{h}" {RECT_ATTRIBS} />')

    for edge in data['edges']:
        points = edge['points']
        class_ = 'edge ' + edge['type']
        if edge['format'] == 'polyline':
            points_str = ' '.join([f'{points[i]},{points[i+1]}' for i in range(0, len(points), 2)])
            print(f'    <polyline class="{class_}" points="{points_str}" {PATH_ATTRIBS} marker-end="url(#arrow-{edge["type"]})" />')
        elif edge['format'] == 'bspline':
            tmp = ''
            tmp += f'    <!-- generated from json type:{edge["type"]} format:{edge["format"]} points:{edge["points"]} -->\n'
            tmp += f'    <path class="{class_}" d="M{points[0]},{points[1]} '
            tmp += 'C' + ' '.join([f'{points[i]},{points[i+1]}' for i in range(2,len(points),2)])
            tmp += f'" {PATH_ATTRIBS} marker-end="url(#arrow-{edge["type"]})"'
            tmp += ' />'
            print(tmp)
        else:
            assert False, f'unknown edge format: {edge["format"]}'

    print(SVG_FOOTER)
