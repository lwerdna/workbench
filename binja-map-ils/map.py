#!/usr/bin/env python

# map from disassembly to BinaryNinja low, medium, high IL
#
# produce a .dot file for use in graphing

import os, sys, re

import binaryninja
from binaryninja.binaryview import BinaryViewType

# get the addresses of every instruction of a function
def get_instruction_addresses(func):
    addrs = []
    for bb in func.basic_blocks:
        bb._buildStartCache()
        addrs.extend(bb._instStarts)
    return sorted(addrs)

def escape(s):
    s = s.replace('>', '&gt;')
    s = s.replace('<', '&lt;')
    s = s.replace('}', '\\}')
    s = s.replace('{', '\\{')
    s = s.replace('"', '\\"')
    s = s.replace('\\n', '\\\\n')
    return s

fpath, symbol = '../testbins/tests-macos-x64-macho', '_loop0'
if sys.argv[2:]:
    fpath, symbol = sys.argv[1:3]
bv = BinaryViewType.get_view_of_file(fpath)
bv.update_analysis_and_wait()
func = bv.get_functions_by_name(symbol)[0]

print('digraph G {')
print('\trankdir=LR;')
print('\tranksep=8;')

#
# assembler
# identified by address
# 1:1 mapping between address and assembler instruction
#
addrs = get_instruction_addresses(func)
print('\t// assembler nodes')
lparts = [f'<{a:08X}> {a:08X}: {escape(bv.get_disassembly(a))}\\l' for a in addrs]
print('\tasm [')
print('\t\tlabel = "' + '|'.join(lparts) + '";')
print('\t\tshape = "record"')
print('\t]')

print('\t// assembler -> lifted edges')
for addr in addrs:
    for instr in func.get_llils_at(addr):
        print(f'\tasm:"{addr:08X}" -> llil:"{instr.instr_index}";')

#
# lifted IL
# identified by object
# 1:n mapping between address and set of lifted instructions
#  (address of first instruction keys the set)
#
#print('\t// lifted nodes')
#lparts = []
#for addr in addrs:
#    for instr in func.get_lifted_ils_at(addr):
#        lparts.append(f'<{instr.instr_index}> {escape(str(instr))}\\l')
#print('\tlifted [')
#print('\t\tlabel = "' + '|'.join(tmp) + '"')
#print('\t\tshape = "record"')
#print('\t]')

#print('\t// lifted -> llil edges')
#for addr in addrs:
#    for instr in func.get_lifted_ils_at(addr):
#        lparts.append(f'<{instr.instr_index}> {escape(str(instr))}\\l')
#
#for addr in addrs:
#    print(f'\tlifted:"{addr:08X}" -> llil:"{addr:08X}";')

#
# low level IL
#
print('\t// low level IL')
lparts = []
for addr in addrs:
    for instr in func.get_llils_at(addr):
        lparts.append(f'<{instr.instr_index}> {escape(str(instr))}\\l')
print('\tllil [')
print('\t\tlabel = "' + '|'.join(lparts) + '"')
print('\t\tshape = "record"')
print('\t]')

print('\t// llil -> mlil edges')
for addr in addrs:
    for instr in func.get_llils_at(addr):
        for m in instr.mlils:
            print(f'\tllil:{instr.instr_index} -> mlil:{m.instr_index};')

#
# medium level IL
#
print('\t// medium level IL')
instrs = sum([[i for i in b] for b in func.mlil], [])
lparts = [f'<{instr.instr_index}> {escape(str(instr))}\\l' for instr in instrs]
print('\tmlil [')
print('\t\tlabel = "' + '|'.join(lparts) + '"')
print('\t\tshape = "record"')
print('\t]')

print('\t// mlil -> hlil edges')
for instr in instrs:
    for h in instr.hlils:
        print(f'\tmlil:{instr.instr_index} -> hlil:{h.instr_index};')

#
# high level IL
#
print('\t// high level IL')
tmp = []
for block in func.hlil:
    for instr in block:
        tmp.append(f'<{instr.instr_index}> {escape(str(instr))}\\l')
        #print(f'\t"mlil_{instr.instr_index}" [')
        #print('\t\tlabel = "' + escape(str(instr)) + '";')
        #print('\t]')
print('\t"hlil" [')
print('\t\tlabel = "' + '|'.join(tmp) + '"')
print('\t\tshape = "record"')
print('\t]')

# done
print('}')
