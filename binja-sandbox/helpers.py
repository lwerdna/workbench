sz_lookup = {1:'.b', 2:'.w', 4:'.d', 8:'.q', 16:'.o'}
sz_lookup_py = {1:'_b', 2:'_w', 4:'_d', 8:'_q', 16:'_o'}

#!/usr/bin/env python
#
# command-line BinaryNinja lifter

import os
import sys
import binascii

from helpers import *

import llil_smt

import binaryninja
from binaryninja import core
from binaryninja import binaryview
from binaryninja import lowlevelil
from binaryninja.enums import LowLevelILOperation

RED = '\x1B[31m'
NORMAL = '\x1B[0m'

# old style, prints tabs to indicate tree structure
# example:
# LLIL_SET_REG
#     sp
#     LLIL_SUB
#         LLIL_REG
#             sp
#         LLIL_CONST
#             20
def il_to_text_tree(il, depth):
    lines = []
    indent = '\t'*depth

    # is an instruction
    if isinstance(il, lowlevelil.LowLevelILInstruction):
        size_suffix = sz_lookup.get(il.size, '?') if il.size else ''
        # handle consts specially
        if il.operation in [LowLevelILOperation.LLIL_CONST, LowLevelILOperation.LLIL_CONST_PTR] and il.size:
            tmp = il.operands[0]
            if tmp < 0: # if neg, convert to pos
                tmp = (1<<(il.size*8))+tmp
            tmp = '0x%X' % tmp if il.size else '%d' % il.size
            lines.append(f'{indent}LLIL_CONST{size_suffix}({tmp})')
        else:
            lines.append(f'{indent}{il.operation.name}{size_suffix}')

        for o in il.operands:
            lines.append(il_to_text_tree(o, depth+1))

    # not an instruction
    else:
        lines.append(indent + str(il))

    return '\n'.join(lines)

def il_to_text_line(il):
    if isinstance(il, lowlevelil.LowLevelILInstruction):
        size_suffix = sz_lookup.get(il.size, '?') if il.size else ''
        # print size-specified IL constants in hex
        if il.operation in [LowLevelILOperation.LLIL_CONST, LowLevelILOperation.LLIL_CONST_PTR] and il.size:
            tmp = il.operands[0]
            if tmp < 0: # if neg, convert to pos
                tmp = (1<<(il.size*8))+tmp
            tmp = '0x%X' % tmp if il.size else '%d' % il.size
            return 'LLIL_CONST%s(%s)' % (size_suffix, tmp)
        else:
            return '%s%s(%s)' % (il.operation.name, size_suffix, ','.join([il_to_text_line(o) for o in il.operands]))
    elif isinstance(il, list):
        return '[' + ','.join([il_to_text_line(x) for x in il]) + ']'
    else:
        return str(il)

def il_to_pylike(il):
    if isinstance(il, lowlevelil.LowLevelILInstruction):
        size_suffix = sz_lookup_py.get(il.size, '?') if il.size else ''
        # print size-specified IL constants in hex
        if il.operation in [LowLevelILOperation.LLIL_CONST, LowLevelILOperation.LLIL_CONST_PTR] and il.size:
            tmp = il.operands[0]
            if tmp < 0: # if neg, convert to pos
                tmp = (1<<(il.size*8))+tmp
            tmp = '0x%X' % tmp if il.size else '%d' % il.size
            return 'LLIL_CONST%s(%s)' % (size_suffix, tmp)
        else:
            return '%s%s(%s)' % (il.operation.name, size_suffix, ','.join([il_to_pylike(o) for o in il.operands]))
    elif isinstance(il, list):
        return '[' + ','.join([il_to_pylike(x) for x in il]) + ']'
    elif isinstance(il, lowlevelil.ILRegister):
        breakpoint()
        return f'ILRegister(\'{il.name}\')'
    else:
        return str(il)

def lift_bytes(arch_name, data, addr=0):
    plat_name = 'linux-' + arch_name
    plat = binaryninja.Platform[plat_name]
    bview = binaryview.BinaryView.new(data)
    bview.platform = plat
    bview.add_function(addr, plat=plat)
    functions = list(bview.functions)
    bview.update_analysis_and_wait()

    assert len(functions) == 1
    func = functions[0]

    result = []
    for block in func.low_level_il:
        for insn in block:
            result.append(insn)
    return result
