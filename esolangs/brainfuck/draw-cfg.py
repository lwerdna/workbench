#!/usr/bin/env python

import os, sys, re, readline, html
from collections import defaultdict

debug = False
for arg in sys.argv[1:]:
    debug = debug or 'debug' in arg

with open(sys.argv[1]) as fp:
    code = fp.read()
code = re.sub(r'\s', ' ', code)

# validate matching []'s
brackets = {}
stack = []
for (i,c) in enumerate(code):
    if c == '[':
        stack.append(i)
    elif c == ']':
        brackets[stack[-1]] = i
        brackets[i] = stack.pop()

if debug:
    print(brackets)

# compute the IP level departures and arrivals

departures = [set() for x in range(len(code))]
arrivals = [set() for x in range(len(code))]
for (src, dst) in brackets.items():
    if src < dst: # is '['
        departures[src].add(src+1)                  # [ to [+1
        departures[src].add(dst+1)                  # [ to ]+1

        arrivals[src+1].add(src)
        arrivals[dst+1].add(src)

    else: # is ']'
        departures[src].add(dst)
        arrivals[dst].add(src)

if debug:
    print('  ip  code      departures arrivals')
    print('  --  ----      ---------- --------')
    for (ip, c) in enumerate(code):
        print('%04d: %03d \'%c\' ' % (ip, ord(c), c) + str(departures[ip]).rjust(12) + ' ' + str(arrivals[ip]).rjust(12))

# calculate the (start, end) pairs for the blocks

starts = [i for i in range(len(code)) if arrivals[i]]
if not starts[0] == 0:
    starts = [0] + starts
starts.append(len(code))
blocks = [(starts[i], code[starts[i]:starts[i+1]]) for i in range(len(starts)-1)]

if debug:
    print('blocks: ', blocks)

edges = set()

for i in range(len(blocks)):
    (src, body) = blocks[i]

    for dst in departures[src + len(body) - 1]:
        # determine edge type
        assert body[-1] in ['[', ']']

        if body[-1] == '[':
            if src + len(body) == dst:
                edge_type = 'while_enter'
            else:
                edge_type = 'while_exit'
        else:
            edge_type = 'continue'

        edges.add((src, dst, edge_type))

    # fall-thru execution
    if body[-1] != ']' and body[-1] != '[' and i < len(blocks)-1:
        edges.add((src, blocks[i+1][0], 'sequential'))

if debug:
    print('edges: ', edges)

if debug:
    sys.exit(-1)

print('digraph g {')
#print('    graph [splines=ortho, nodesep=1];')
print('    node [fontname="Courier New" fontsize="8"];')
print('    // define vertices')
for (start, body) in blocks:
    color = 'white'
    if '.' in body:
        color = 'darkgrey'
        #color = 'aqua'
        #color = 'grey50'
        pass
    if ',' in body:
        #color = 'red'
        #color = 'grey40'
        pass
    if '.' in body or ',' in body:
        color = 'darkgrey'
        pass

    if start + len(body) >= len(code):
        color = 'crimson'

    #shape = 'box'
    shape = 'Mrecord'
    if code[start] == '[':
        #shape = 'diamond'
        pass
    if '.' in body or ',' in body:
        #shape = 'box3d'
        shape = 'box'

    extra = '';
    extra += '' if color == 'white' else ' fillcolor="%s" style="filled"' % color
    extra += '' if not shape else ' shape="%s"' % shape
    label = '\\l'.join([body[i:i+16] for i in range(0, len(body), 16)])
    print('    %d [shape="Mrecord" label="%d:\\l%s"%s];' % (start, start, html.escape(label), extra))
print('    // define edges')
for (src, dst, etype) in edges:
    extra = ''
    if etype == 'sequential':
        extra = ' [arrowhead=none]'
    if etype == 'continue':
        extra = ' [style=dashed, color=grey]'

    print('    %d -> %d%s;' % (src, dst, extra))
print('}')

