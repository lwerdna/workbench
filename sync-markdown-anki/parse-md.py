#!/usr/bin/env python

import os
import sys

import commonmark

def collect_children(node):
    current = node.first_child
    while current:
        yield current
        current = current.nxt

def collect_ancestors(node):
    current = node.parent
    while current:
        yield current
        current = current.parent

def mydump(node, depth=0):
    indent = '  '*depth

    pos_str = ''
    if node.sourcepos:
        pos_str = f'{node.sourcepos[0][0]},{node.sourcepos[0][1]}-{node.sourcepos[1][0]},{node.sourcepos[1][1]}'
    print(f'{indent}{node.t} {pos_str} llb:{node.last_line_blank}')

    for child in collect_children(node):
        mydump(child, depth+1)

def render_markdown(node):
    children = list(collect_children(node))

    result = ''

    if node.t == 'document':
        for child in children:
            result += render_markdown(child)
    elif node.t == 'paragraph':
        for child in children:
            result += render_markdown(child)
    elif node.t == 'heading':
        result = '#'*node.level + ''.join(render_markdown(c) for c in children) + '\n'
    elif node.t == 'text':
        result = node.literal 
    elif node.t == 'code_block':
        if node.is_fenced:
            result = node.fence_char * node.fence_length + node.info + '\n'
            result += node.literal
            result += node.fence_char * node.fence_length
        else:
            result = '\n'.join(f'    {line}' for line in node.literal.split('\n'))
    elif node.t == 'softbreak':
        result += '\n'
    elif node.t == 'code':
        result = '`' + node.literal + '`'
    elif node.t == 'list':
        for child in children:
            result += render_markdown(child)
            result += '\n'
    elif node.t == 'item':
        if node.list_data['type'] == 'bullet':
            bullet = node.list_data['bullet_char']
        elif node.list_data['type'] == 'ordered':
            bullet = node.list_data['start']
        else:
            breakpoint()
            pass

        for child in children:
            result += f'{bullet} ' + render_markdown(child)

    elif node.t == 'link':
        assert len(children) == 1
        result = f'[{node.destination}]({render_markdown(node.first_child)})'
    elif node.t == 'emph':
        assert len(children) == 1
        result = '_' + render_markdown(node.first_child) + '_'
    elif node.t == 'strong':
        assert len(children) == 1
        result = '**' + render_markdown(node.first_child) + '**'
    elif node.t == 'html_inline':
        result = node.literal
    else:
        print(f'unknown type: {node.t}')
        print(node.pretty())
        breakpoint()

    # decide whether to add space after this block
    block = False
    if node.t == 'heading':
        block = True
    if node.t == 'code_block':
        block = True
    if node.t == 'paragraph':
        if node.parent.t == 'document':
            if node != node.parent.last_child:
                block = True
        else:
            if not list in [anc.t for anc in collect_ancestors(node)]:
                block = True

    if block:
        while not result.endswith('\n\n'):
            result = result + '\n'

    return result

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
