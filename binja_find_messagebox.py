# find messages printed to messagebox
#
# this is intended to be loaded from the binja console
#
# >>> sys.path.append('/path/to/this/script')
# >>> import binja_find_messagebox
# >>> binja_find_messagebox.go(bv)
#
# you can edit/reload with:
#
# >>> import importlib
# >>> importlib.reload(binja_find_messagebox)

from binaryninja import *

def go(bv):
    for func in bv.functions:
        for block in func.mlil:
            for instr in block:
                if instr.operation != MediumLevelILOperation.MLIL_CALL: continue
                if instr.operands[1].tokens[0].text != 'MessageBoxA': continue

                (hWnd, lpText, lpCaption, uType) = instr.operands[2]
                string_ref = bv.get_string_at(lpText.value.value)
                print('%08X: MessageBoxA(..., "%s", ...)' % (instr.address, string_ref.value))
