#!/usr/bin/env python

# Q: Can the linear disassembly cursor and lines stuff be demonstrated?
# A: The “position” or “cursor” in the context of this linear disassembly stuff is not the text lines, it’s an index on linear disassembly “elements”, where each element can have multiple lines.

import sys, time
import binaryninja
from binaryninja import lineardisassembly, function
from binaryninja.enums import InstructionTextTokenType

fpath = '/bin/ls' if len(sys.argv)==1 else sys.argv[1]
with binaryninja.open_view(fpath) as bv:
    #bv_end = bv.start + len(bv) - 1
    #fmt = '%08X' if (bv_end < 0x100000000) else '%016X'

    settings = function.DisassemblySettings()
    obj = lineardisassembly.LinearViewObject.disassembly(bv, settings)
    cursor = lineardisassembly.LinearViewCursor(obj)

    i = 0
    while(True):
        lines = bv.get_next_linear_disassembly_lines(cursor)
        print('cursor position %d has %d lines:' % (i, len(lines)))
        if len(lines) == 0:
            break
        for l in lines:
            print('    ' + str(l))
        i += 1
