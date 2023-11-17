#!/usr/bin/env python

import re
import os
import sys

from binaryninja.enums import *
from binaryninja import highlevelil, core

# NOTES:
# get highest expression index
#   core.BNGetHighLevelILExprCount(current_il_function.handle)
# get root expression index
#   core.BNGetHighLevelILRootExpr(current_il_function.handle)
# convert expression index into an instruction
#   HighLevelILInstruction.create(current_il_function, <expr_index>)
#    (calls core.BNGetHighLevelILInstructionForExpr)

def escape(label):
    label = label.replace('\\n', '\\\\n')
    label = label.replace('"', '\\"')
    return label

def make_label(node):
    if isinstance(node, highlevelil.HighLevelILInstruction):
        if node.operation == HighLevelILOperation.HLIL_VAR_DECLARE:
            result = f'VAR_DECLARE "{node.var}"'
        elif node.operation == HighLevelILOperation.HLIL_STRUCT_FIELD:
            result = f'STRUCT_FIELD ({node.src}+{node.offset})'
        elif node.operation == HighLevelILOperation.HLIL_CONST_PTR:
            result = f'CONST_PTR (0x{node.constant:X})'
        else:
            tmp = node.operation.name
            assert tmp.startswith('HLIL_')
            result = tmp[5:]

        return escape(f'{node.expr_index}: ' + result)

    else:
        type_label = re.match(r'^<class \'(.*)\'>$', str(type(node))).group(1).split('.')[-1]
        return f'{type_label}: {node}'

def children(node):
    # see api/python/highlevelil.py
    if isinstance(node, highlevelil.HighLevelILInstruction):
        if node.operation == HighLevelILOperation.HLIL_BLOCK: # class HighLevelILBasicBlock
            children = node.body
        elif node.operation == HighLevelILOperation.HLIL_IF: # class HighLevelILBasicIf
            children = [node.condition, node.true, node.false]
        elif node.operation == HighLevelILOperation.HLIL_WHILE: # class HighLevelILBasicWhile
            children = [node.condition, node.body]
        elif node.operation == HighLevelILOperation.HLIL_FOR: # class HighLevelILFor
            children = [node.init, node.condition, node.update, node.body]
        elif node.operation == HighLevelILOperation.HLIL_RET:
            children = node.operands[0] # is itself a list
        #elif node.operation == HighLevelILOperation.HLIL_CONST:
        #    children = [] # do not generate a node for the int, just put it in the CONST's label
        else:
            children = node.operands
    else:
        children = []
  
    return children

def traverse_preorder(root):
    result = [root]
    for c in children(root):
        result.extend(traverse_preorder(c))
    return result

def get_dot_function(func):
    tmp_id = 0

    dot = []
    dot.append('digraph G {')

    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')

    # collect all hlil_nodes
    if 1:
        n_exprs = core.BNGetHighLevelILExprCount(func.handle)
        hlil_nodes = [highlevelil.HighLevelILInstruction.create(func, i) for i in range(n_exprs)]
    else:
        hlil_nodes = []
        for instr in func.instructions:
            offspring = [o for o in traverse_preorder(instr) if isinstance(o, highlevelil.HighLevelILInstruction)]
            hlil_nodes.extend(offspring)

    # declare all nodes
    dot.append('// nodes')
    # HLIL nodes
    for node in hlil_nodes:
        attrs = [f'label="{make_label(node)}"', 'shape=box']
        if node.parent == None and not isinstance(node, highlevelil.HighLevelILBlock):
            attrs.append('fillcolor=red')
            attrs.append('style=filled')
        dot.append(f'expr_index_{node.expr_index} [' + ' '.join(attrs) + '];')
    # instruction indices
    for i in range(len(func)):
        dot.append(f'instr_{i} [label="instructions[{i}]" fillcolor=green style=filled]')
    # root
    dot.append(f'root [shape=diamond fillcolor=green style=filled];')

    dot.append('// edges')
    # hlil->hlil edges
    for parent in hlil_nodes:
        for child in children(parent):
            if isinstance(child, highlevelil.HighLevelILInstruction):
                dot.append(f'expr_index_{parent.expr_index} -> expr_index_{child.expr_index};')
            else:
                # create tmp node for this non-HLIL
                dot.append(f'tmp_{tmp_id} [label="{make_label(child)}" fillcolor=grey style=filled]')
                dot.append(f'expr_index_{parent.expr_index} -> tmp_{tmp_id}')
                tmp_id += 1

    # instruction[x] -> hlil
    for i, instr in enumerate(func.instructions):
        dot.append(f'instr_{i} -> expr_index_{instr.expr_index}')
    # root -> hlil
    root_expr_index = core.BNGetHighLevelILRootExpr(func.handle)
    dot.append(f'root -> expr_index_{root_expr_index}')

    dot.append('}')

    return '\n'.join(dot)

# boilerplate to get at default variables
from binaryninjaui import UIContext
active_ctx = UIContext.activeContext()
view_frame = active_ctx.getCurrentViewFrame()
view_location = view_frame.getViewLocation()
active_il_index = view_location.getInstrIndex()
action_ctx = active_ctx.contentActionHandler().actionContext()
current_function = action_ctx.function
current_hlil = current_function.hlil
hlil_instr = current_hlil[active_il_index]

print(current_hlil)
dot = get_dot_function(current_hlil)
with open('/tmp/tmp.dot', 'w') as fp:
    fp.write(dot)

print('done')



