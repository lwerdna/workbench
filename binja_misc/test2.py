#!/usr/bin/env python

# Q: can you get a full text version of linear disassembly?
# A: yes

import sys, time
import binaryninja
from binaryninja.enums import InstructionTextTokenType

fpath = '/bin/ls' if len(sys.argv)==1 else sys.argv[1]
with binaryninja.open_view(fpath) as bv:
    #bv_end = bv.start + len(bv) - 1
    #fmt = '%08X' if (bv_end < 0x100000000) else '%016X'

    for ldl in bv.get_linear_disassembly(): # LinearDisassemblyLine
        dtl = ldl.contents # DisassemblyTextLine

        # filter out eggplant emoji's
        tokens = [t for t in dtl.tokens if t.type != InstructionTextTokenType.TagToken]
        text = ''.join([t.text for t in tokens])
        #print('%08X: %s' % (dtl.address, text))
        print(text)
