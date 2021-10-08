#!/usr/bin/env python

import os, sys, re

from helpers import *

import binaryninja
from binaryninja.binaryview import BinaryViewType
from binaryninja.enums import *

(bv, func) = quick_get_func()

#breakpoint()

func_mlil = func.mlil
# current_func.mlil.ssa_vars      // returns []
# current_func.mlil.ssa_form.vars // returns what's expected
func_mlil_ssa = func_mlil.ssa_form

print('VARS:')

# v:binaryninja.function.Variable (NOT binaryninja.mediumlevelil.SSAVariable)
for v in func_mlil_ssa.vars:
    source_descr = ''
    if v.source_type == VariableSourceType.RegisterVariableSourceType:
        if v.storage & 0x80000000:
            source_descr = '(regid=<temp>)'
        else:
            source_descr = '(regid=%d "%s")' % (v.storage, bv.arch.get_reg_name(v.storage))
    elif v.source_type == VariableSourceType.StackVariableSourceType:
        source_descr = '(src:stack %d)' % v.storage
    elif v.source_type == VariableSourceType.FlagVariableSourceType:
        source_descr = '(src:flag %d)' % v.storage
    else:
        assert False

    print('"%s" %s defined at:' % (v, source_descr))

    # def sites is list of IL instructions that define ANY SSA VERSION
    # of this variable
    instrs = func_mlil_ssa.get_var_definitions(v) # [binaryninja.mediumlevelil.MediumLevelILInstruction]
    for instr in instrs:
        print('\t%08X: %s' % (instr.address, instr))

print('all version 0 SSA vars with a definition site:')
for var in [x for x in func_mlil_ssa.ssa_vars if x.version==0]:
    print('var: %s' % var)
    def_instr = func_mlil_ssa.get_ssa_var_definition(var)
    if not def_instr: continue
    print('\tdefined %08X: %s' % (def_instr.address, def_instr))

#print('all version 1 SSA vars:')
#for instr in [x for x in func_mlil_ssa.ssa_vars if x.version==1]:
#    print(instr)

print('can intercept args at:')
for instr in func_mlil.instructions:
    # we are looking for
    #   MediumLevelILInstruction (.operation = MLIL_SET_VAR)
    #     binaryninja.function.Variable
    #     MediumLevelILInstruction (.operation = MLIL_VAR)
    #       binaryninja.function.Variable (with .name /arg\d+/) 
    #breakpoint()
    if instr.operation != MediumLevelILOperation.MLIL_SET_VAR: continue
    if instr.operands[1].operation != MediumLevelILOperation.MLIL_VAR: continue
    if not re.match(r'^arg\d+', instr.operands[1].src.name): continue
    print('\t%08X: %s' % (instr.address, instr))

    
