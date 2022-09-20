#!/usr/bin/env python

import os
import sys

import binaryninja
from binaryninja.enums import *
from binaryninja import highlevelil

def escape(label):
    label = label.replace('\\n', '\\\\n')
    label = label.replace('"', '\\"')
    return label

def make_label(node):
    if node.operation == HighLevelILOperation.HLIL_VAR:
        result = f'VAR "{node.var}"'
    elif node.operation == HighLevelILOperation.HLIL_VAR_DECLARE:
        result = f'VAR_DECLARE "{node.var}"'
    elif node.operation == HighLevelILOperation.HLIL_STRUCT_FIELD:
        result = f'STRUCT_FIELD ({node.src}+{node.offset})'
    elif node.operation == HighLevelILOperation.HLIL_CONST:
        result = f'CONST ({node.constant})'
    elif node.operation == HighLevelILOperation.HLIL_CONST_PTR:
        result = f'CONST_PTR (0x{node.constant:X})'
    else:
        tmp = node.operation.name
        assert tmp.startswith('HLIL_')
        result = tmp[5:]

    return escape(result)

def ast_children(root):
    # see api/python/highlevelil.py
    if root.operation == HighLevelILOperation.HLIL_BLOCK: # class HighLevelILBasicBlock
        children = root.body
    elif root.operation == HighLevelILOperation.HLIL_IF: # class HighLevelILBasicIf
        children = [root.condition, root.true, root.false]
    elif root.operation == HighLevelILOperation.HLIL_WHILE: # class HighLevelILBasicWhile
        children = [root.condition, root.body]
    elif root.operation == HighLevelILOperation.HLIL_FOR: # class HighLevelILFor
        children = [root.init, root.condition, root.update, root.body]
    else:
        children = root.operands
    return [c for c in children if isinstance(c, highlevelil.HighLevelILInstruction)]

def ast_traverse_preorder(root):
    result = [root]
    for c in ast_children(root):
        result.extend(ast_traverse_preorder(c))
    return result

def ast_get_dot(root):
    nodes = ast_traverse_preorder(root)
    lookup = {obj:i for (i,obj) in enumerate(nodes)}

    dot = []
    dot.append('digraph G {')

    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')

    dot.append('// nodes')
    for (node, i) in lookup.items():
        if not hasattr(node, 'operation'):
            breakpoint()
        label = make_label(node)
        dot.append(f'{i} [label="{label}"];')

    dot.append('// edges')
    for (a, i) in lookup.items():
        attrs = []
        for b in ast_children(a):
            dot.append(f'{i} -> {lookup[b]} [' + ' '.join(attrs) + '];')

    dot.append('}')

    return '\n'.join(dot)

if __name__ == '__main__':
    # target file and symbol
    fpath = os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/testbins/tests-macos-x64-macho')
    symbol = '_dream_cfg'
    if sys.argv[2:]:
        fpath, symbol = sys.argv[1:3]

    # get hlil function
    bv = binaryninja.open_view(fpath)
    func = bv.get_functions_by_name(symbol)[0].hlil

    # generate graph
    dot = ast_get_dot(func.root)
    print(dot)
