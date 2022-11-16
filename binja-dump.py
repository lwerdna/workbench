#!/usr/bin/env python

# dump as much as possible that binja knows about a binary

import sys, time
import binaryninja
from binaryninja import lineardisassembly, function
from binaryninja.enums import InstructionTextTokenType, DisassemblyOption

def print_divider(text):
    print()
    print('--------------------------------------------------------------------------------')
    print(text)
    print('--------------------------------------------------------------------------------')

def print_cursor(cursor):
    i = 0
    while(True):
        lines = bv.get_next_linear_disassembly_lines(cursor)
        if len(lines) == 0:
            break
        for l in lines:
            print('    ' + str(l))
        i += 1

fpath = '/bin/ls' if len(sys.argv)==1 else sys.argv[1]

with binaryninja.open_view(fpath) as bv:
    settings = function.DisassemblySettings()
    settings.set_option(DisassemblyOption.ShowAddress)
    settings.set_option(DisassemblyOption.ShowOpcode)
    settings.set_option(DisassemblyOption.ExpandLongOpcode)
    settings.set_option(DisassemblyOption.ShowVariablesAtTopOfGraph)
    settings.set_option(DisassemblyOption.ShowVariableTypesWhenAssigned)
    settings.set_option(DisassemblyOption.ShowCallParameterNames)
    settings.set_option(DisassemblyOption.ShowRegisterHighlight)
    settings.set_option(DisassemblyOption.ShowFunctionAddress)
    settings.set_option(DisassemblyOption.ShowFunctionHeader)
    settings.set_option(DisassemblyOption.GroupLinearDisassemblyFunctions)
    settings.set_option(DisassemblyOption.HighLevelILLinearDisassembly)
    settings.set_option(DisassemblyOption.WaitForIL)
    settings.set_option(DisassemblyOption.IndentHLILBody)
    settings.set_option(DisassemblyOption.ShowFlagUsage)
    settings.set_option(DisassemblyOption.ShowStackPointer)

    print_divider('setup')
    print('python binaryninja module path: ' + binaryninja.__file__)
    print('core_version(): ' + binaryninja.core_version())
    print('core_build_id(): %d (0x%X)' % (binaryninja.core_build_id(), binaryninja.core_build_id()))

    print_divider('architecture')
    print('registers:')
    for (name, reginfo) in bv.arch.regs.items():
        print('name:%s index:%d offset:%d size:%d full_width_reg:%s' % \
            (name, reginfo.index, reginfo.offset, reginfo.size, reginfo.full_width_reg))

    print_divider('disassembly')
    obj = lineardisassembly.LinearViewObject.disassembly(bv, settings)
    cursor = lineardisassembly.LinearViewCursor(obj)
    print_cursor(cursor)

#    print_divider('lifted il')
#    obj = lineardisassembly.LinearViewObject.lifted_il(bv, settings)
#    cursor = lineardisassembly.LinearViewCursor(obj)
#    print_cursor(cursor)

    print_divider('low level il')
    obj = lineardisassembly.LinearViewObject.llil(bv, settings)
    cursor = lineardisassembly.LinearViewCursor(obj)
    print_cursor(cursor)

#    print_divider('low level il ssa')
#    obj = lineardisassembly.LinearViewObject.llil_ssa_form(bv, settings)
#    cursor = lineardisassembly.LinearViewCursor(obj)
#    print_cursor(cursor)

    print_divider('medium level il')
    obj = lineardisassembly.LinearViewObject.mlil_ssa_form(bv, settings)
    cursor = lineardisassembly.LinearViewCursor(obj)
    print_cursor(cursor)

#    print_divider('medium level il ssa')
#    obj = lineardisassembly.LinearViewObject.mlil_ssa_form(bv, settings)
#    cursor = lineardisassembly.LinearViewCursor(obj)
#    print_cursor(cursor)

#    print_divider('mapped medium level lil')
#    obj = lineardisassembly.LinearViewObject.mmlil_ssa_form(bv, settings)
#    cursor = lineardisassembly.LinearViewCursor(obj)
#    print_cursor(cursor)

    print_divider('high level il')
    obj = lineardisassembly.LinearViewObject.hlil(bv, settings)
    cursor = lineardisassembly.LinearViewCursor(obj)
    print_cursor(cursor)

#    print_divider('high level il ssa')
#    obj = lineardisassembly.LinearViewObject.mlil_ssa_form(bv, settings)
#    cursor = lineardisassembly.LinearViewCursor(obj)
#    print_cursor(cursor)
