#!/usr/bin/env python

# Q: Can the linear disassembly cursor and lines stuff be demonstrated?
# A: The “position” or “cursor” in the context of this linear disassembly stuff is not the text lines, it’s an index on linear disassembly “elements”, where each element can have multiple lines.

import sys, time

from collections import OrderedDict

import binaryninja
from binaryninja import lineardisassembly, function
from binaryninja.enums import InstructionTextTokenType, DisassemblyOption

def explore_pseudoc(func):
    bview = func.view
    settings = function.DisassemblySettings()
    # lvo: binaryninja.lineardisassembly.LinearViewObject
    lvo = lineardisassembly.LinearViewObject.disassembly(bview, settings)
    # lr: binaryninja.lineardisassembly.LinearViewObject
    lr = lvo.single_function_language_representation(func)
    cursor = lineardisassembly.LinearViewCursor(lr)

    dumped = []
    lookup = OrderedDict()
    while(True):
        linear_lines = bview.get_next_linear_disassembly_lines(cursor)
        if len(linear_lines) == 0: break

        # line: binaryninja.lineardisassembly.LinearDisassemblyLine
        for line in linear_lines:
            # dtl: binaryninja.function.DisassemblyTextLine
            dtl = line.contents

            dumped.append(str(dtl))

            if not dtl.address in lookup: lookup[dtl.address] = []
            lookup[dtl.address].append(str(dtl))

    return dumped, lookup

def get_pseudoc_for_func(func):
    dumped, _ = explore_pseudoc(func)
    return dumped

if 0:
    fpath = '/bin/ls' if len(sys.argv)==1 else sys.argv[1]
    with binaryninja.open_view(fpath) as bv:
        func = bv.get_functions_by_name('sub_1000039d3')[0]
        #breakpoint()
        lines = get_pseudoc_for_func(func)
        print('\n'.join(lines))

        dumped, lookup = explore_pseudoc(func)

        for bb in func.hlil:
            for instr in bb:
                print(f'// HLIL: {instr}')
                print('\n'.join(lookup[instr.address]))
else:
    fpath = '../testbins/tests-linux-x64-elf' if len(sys.argv)==1 else sys.argv[1]
    with binaryninja.open_view(fpath) as bv:
        for func in bv.functions:
            lines, lookup = explore_pseudoc(func)

            print(f'-------- {func} PSEUDO-C DUMP --------')
            print('\n'.join(lines))

            print(f'-------- {func} HLIL DUMP W/ PSEUDO-C COMMENTS --------')
            for bb in func.hlil:
                for instr in bb:
                    print(f'// HLIL: {instr}')
                    if hasattr(instr, 'address'):
                        if instr.address in lookup:
                            print('\n'.join(lookup[instr.address]))
                        else:
                            print(f'no obvious pseudo-c corresponding to address 0x{instr.address:X}')
                    else:
                        print('no .address to look up anything')
    
