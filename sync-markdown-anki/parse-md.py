#!/usr/bin/env python

import os
import sys

import commonmark

from helpers import *

def mydump(node, depth=0):
    indent = '  '*depth

    pos_str = ''
    if node.sourcepos:
        pos_str = f'{node.sourcepos[0][0]},{node.sourcepos[0][1]}-{node.sourcepos[1][0]},{node.sourcepos[1][1]}'
    print(f'{indent}{node.t} {pos_str} llb:{node.last_line_blank}')

    for child in collect_children(node):
        mydump(child, depth+1)


if __name__ == '__main__':
    command = sys.argv[1]
    fpath = 'Information.md'
    if sys.argv[2:]:
        fpath = sys.argv[2]

    parser = commonmark.Parser()
    ast = parser.parse(open(fpath).read())

    if command == 'html':
        # this is how the ast would be used to generate HTML
        renderer = commonmark.HtmlRenderer()
        html = renderer.render(ast)
        print(html)

    elif command == 'dump':
        #print(commonmark.dumpJSON(ast))
        #print(commonmark.dumpAST(ast))
        mydump(ast)

    elif command == 'md':
        md = render_markdown(ast)
        print(md)
