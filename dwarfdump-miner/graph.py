#!/usr/bin/env python

import os, sys, re

from helpers import *

# superclass DNode to add dot-related features
class GraphNode(DNode):
    def dot_label(self):
        blacklist = set(['DW_AT_decl_file', 'DW_AT_decl_line'])

        lines = []
        lines.append('0x%X: %s' % (self.offset, self.tag))
        if name := self.attributes.get('DW_AT_name', None):
            lines.append(dot_label_escape(name))
        #for (name, value) in self.attributes.items():
        #    if name in blacklist:
        #        continue
        #    lines.append('%s: %s' % (name.replace('DW_AT_', ''), value))
        return '\\l'.join(lines)

    def dot_id(self):
        return str(self.offset)

def graph(nodes):
    ignore_tag_compile_unit = True

    tag_to_palette = {
        'DW_TAG_typedef': 1, 'DW_TAG_const_type': 1, 'DW_TAG_pointer_type': 1,
        'DW_TAG_array_type': 2,
        'DW_TAG_subrange_type': 2,
        'DW_TAG_structure_type': 4, 'DW_TAG_subprogram': 5, 'DW_TAG_formal_parameter': 6,
        'DW_TAG_member': 7, 'DW_TAG_base_type': 8 }

    offset_to_node = {n.offset: n for n in nodes}

    print('digraph G {')
    print('\trankdir="LR";')
    print('\tnode [colorscheme=pastel28];')

    # do nodes
    print('\t// nodes')
    for node in nodes:
        if ignore_tag_compile_unit and node.tag == 'DW_TAG_compile_unit':
            continue

        extra = ''
        if node.tag in tag_to_palette:
            extra = ' color=%d, style=filled' % tag_to_palette[node.tag]

        print('\t%s [label="%s" shape="Mrecord"%s];' % (node.dot_id(), node.dot_label(), extra))

    # do edges
    print()
    print('\t// edges')
    for src in nodes:
        if ignore_tag_compile_unit and src.tag == 'DW_TAG_compile_unit':
            continue
        for dst in src.children:
            print('\t%s -> %s;' % (src.dot_id(), dst.dot_id()))
        
        if src.type:
            dst = src.type
            print('\t%s -> %s [style=dashed, color=darkgray];' % (src.dot_id(), dst.dot_id()))

    print('}')

if __name__ == '__main__':
    fpath = sys.argv[1]
    task = sys.argv[2]

    start = None
    if m := re.match(r'^--structure=(.*)$', task):
        struct_name = m.group(1)
        start = dwarfdump_structure(fpath, struct_name, GraphNode)
    if m := re.match(r'^--function=(.*)$', task):
        func_name = m.group(1)
        start = dwarfdump_function(fpath, func_name, GraphNode)
    assert start

    pool = reachable(start)
    graph(pool)

