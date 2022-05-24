#!/usr/bin/env python

import re, os, sys
import json
import copy

from helpers import *

DPI = 96.0

def make_dot(data, gv_subproc='dot'):
    result = ''
    result += f'// gv_subproc: {gv_subproc}\n'
    result += 'digraph G {\n'
    result += '  nodesep = 0.2;\n'
    result += '  ranksep = 0.2;\n'
    if gv_subproc == 'dot_ortho':
        result += '  graph [splines=ortho]\n'
    result += '  edge [arrowhead="none"]\n'
    result += '  // nodes\n'

    for (i, entry) in enumerate(data['blocks']):
        (x,y,w,h) = entry['rect']
        result += f'  bb{i} [label="bb{i}" shape="rectangle" fixedsize="rectangle"'
        result += f' width="{w/DPI}" height="{h/DPI}"];\n'

    result += '  // edges\n'

    for (src, entry) in enumerate(data['blocks']):
        for [dst, branch_type] in entry['targets']:
            result += f'  bb{src} -> bb{dst} [label="{branch_type}"];\n'

    result += '}\n'

    return result

#  INPUT: json from like `dot -Tjson ...`
# OUTPUT: [
#           (<x>, <y>, <w>, <h>), // coordinates of block0
#           (<x>, <y>, <w>, <h>), // coordinates of block1
#           ...         // ...
#         ]
def read_graphviz_txt(fpath):
    blocks = []
    edges = []

    lines = None
    with open(fpath) as fp:
        lines = fp.readlines()

    for line in lines:
        # line like:
        line = line.strip()
        toks = line.split(' ')
        assert toks[0] in ['graph', 'node', 'edge', 'stop']

        if toks[0] == 'node':
            bbidx = int(re.match(r'^bb(\d+)$', toks[1]).group(1))
            [x,y,w,h] = [float(x) for x in toks[2:2+4]]

            while bbidx >= len(blocks):
                blocks.append(None)

            # change from inches to pixels
            [x,y,w,h] = [x*DPI for x in [x,y,w,h]]
            # change from center-of-rect to topleft-corner-of-rect
            [x,y] = [x-w/2, y-h/2]
            # round to avoid figures like 168.67200000000003 or 395.99999999999994
            [x,y,w,h] = [round(x,4) for x in [x,y,w,h]]

            blocks[bbidx] = (x,y,w,h)

        elif toks[0] == 'edge':
            parsed = edgetxt_parse(line)
            values = []
            for (x,y) in parsed['points']:
                values.append(x*DPI)
                values.append(y*DPI)
            values = [round(v,4) for v in values]
            edges.append({'type':parsed['label'], 'format':'bspline', 'points':values})

    return (blocks, edges)

if __name__ == '__main__':
    fpaths = []
    if sys.argv[1:]:
        fpaths = [sys.argv[1]]
    else:
        fpaths = [f'./datas/{f}' for f in os.listdir('./datas') if f.endswith('_binja.json')]

    # testing:
    #fpaths = ['./datas/_print_2path_binja.json']

    for fpath in fpaths:
        print(f'opening: {fpath}')
        data_binja = load_json(fpath)

        for graphviz_subproc in ['dot', 'dot_ortho']:
        #for graphviz_subproc in ['dot_ortho']:
            # ask graphviz where it would layout the blocks
            dot = make_dot(data_binja, graphviz_subproc)
            with open('/tmp/tmp.dot', 'w') as fp:
                fp.write(dot)

            os.system('dot -y -Tplain /tmp/tmp.dot > /tmp/tmp.txt')
            (gv_blocks, gv_edges) = read_graphviz_txt('/tmp/tmp.txt')

            # add graphviz block info to data
            data = copy.deepcopy(data_binja)
            for (i, (x,y,w,h)) in enumerate(gv_blocks):
                data['blocks'][i] = {'rect': [x,y,w,h], 'targets': []};
                #data['blocks'][i]['dot'] = [x,y,w,h]

            # add graphviz edge info to data
            data['edges'] = []
            for control_points in gv_edges:
                data['edges'].append(control_points)

            #
            data['width'] = round(max([(e['rect'][0] + e['rect'][2]) for e in data['blocks']]), 4)
            data['height'] = round(max([(e['rect'][1] + e['rect'][3]) for e in data['blocks']]), 4)

            # output

            tmp = fpath.replace('_binja.json', f'_{graphviz_subproc}.json')
            print(f'writing: {tmp}')
            with open(tmp, 'w') as fp:
                fp.write(json.dumps(data, indent=2))
            #fpath_output = fpath_input.replace('-binja.json', '-graphviz.json')
