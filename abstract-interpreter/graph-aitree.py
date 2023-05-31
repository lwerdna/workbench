#!/usr/bin/env python

import os
import sys

from helpers import *

ticket = 0
def make_tnode_re(tree, precond):
    global ticket

    assert type(tree) == TreeNode
    label = tree.label
    print(f'\t{id(tree)} [label="{label}"]')

    for child in tree.children:
        if type(child) == TreeNode:
            child_id = id(child)
            make_tnode_re(child, precond)
        else:
            child_id = f'leaf_{ticket}'
            print(f'\t{child_id} [label="{child}" shape="rectangle"]')
            ticket += 1

        edge_label = ''
        edge_dir = 'none'
        if type(child) == TreeNode:
            if va := child.abstr_interp(precond):
                edge_label = str(va)
                edge_dir = 'back'
        print(f'\t{id(tree)} -> {child_id} [dir="{edge_dir}" label="{edge_label}"]')

def make_tnode(tree, precond):
    print('digraph G {')
    make_tnode_re(tree, precond)
    print('}')

def htmlify(x):
    if x == None:
        return ''
    x = x.replace('<', '&lt;')
    x = x.replace('>', '&gt;')
    x = x.replace('\n', '<br />')
    return x

if __name__ == '__main__':
    with open(sys.argv[1], "r") as source:
        lines = source.readlines()

    precond, postcond = parse_conditions(lines)

    tree = refine(parse(''.join(lines)), TreeNode)
    tree = TreeNode('start', None, tree)

    # run abstract interpretation
    tree.AI(precond)

    nodes = tree.nodes_re()
    print('digraph G {')
    print('\t// global settings')
    #print('\tedge [fontname="Courier"];')
    print('\t// nodes')
    for node in nodes:
        print(f'\t{id(node)} [label="{node.str_short()}"];')
    print('\t// edges')
    for node in nodes:
        #if node.log_pres:
        #    assert len(node.log_pres) == len(node.log_posts), breakpoint()

        for (i, child) in enumerate(node.children):
            label = '<table cellspacing="0">'
            if node.log_pres and i < len(node.log_pres):
                label += f'<tr><td bgcolor="lightblue">{htmlify(node.log_pres[i])}</td></tr>'
            if node.log_posts and i < len(node.log_posts):
                color = 'lightpink'
                if node.str_short() == 'start':
                    color = 'lightgreen'

                label += f'<tr><td bgcolor="{color}">'
                label += htmlify(node.log_posts[i])
                label += f'</td></tr>'

            label += '</table>'

            # graphviz doesn't allow empty tables
            if label == '<table cellspacing="0"></table>':
                label = '""'
            else:
                label = f'<{label}>'

            print(f'\t{id(node)} -> {id(child)} [dir="none" label={label}];')

    # get abstract interpretation edges
    #print('logged preconditions')
    print('}')

