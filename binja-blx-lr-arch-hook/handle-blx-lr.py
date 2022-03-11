# BinaryNinja plugin to treat armv7 "blx lr" as a return
#
# https://docs.binary.ninja/guide/plugins.html

from binaryninja.architecture import Architecture, ArchitectureHook
from binaryninja.function import InstructionInfo, InstructionTextToken
from binaryninja.enums import BranchType, InstructionTextTokenType

encoding = b'\x3e\xff\x2f\xe1' # blx lr

class BlxLrOverride(ArchitectureHook):
    def __init__(self, arch):
        super(BlxLrOverride, self).__init__(arch)
        self.arch = arch

    # override disassembly
#    def get_instruction_text(self, data, addr):
#        if not data.startswith(encoding):
#            result = super(BlxLrOverride, self).get_instruction_text(data, addr)
#            if result and result[0] == None:
#                result = None
#            return result
#
#        result = []
#        result.append(InstructionTextToken(InstructionTextTokenType.TextToken, "test"))
#        return result, 4

    # override "get_branch_behavior()"
    def get_instruction_info(self, data, addr):
        if not data.startswith(encoding):
            return super(BlxLrOverride, self).get_instruction_info(data, addr)

        #print('%08X: informing Binja blx lr is a function return' % addr)
        result = InstructionInfo()
        result.length = 4
        result.add_branch(BranchType.FunctionReturn)
        return result

    # override lift
    def get_instruction_low_level_il(self, data, addr, il):
        if not data.startswith(encoding):
            return super(BlxLrOverride, self).get_instruction_low_level_il(data, addr, il)
        
        #print('%08X: lifting blx lr as a jump to lr' % addr)
        il.append(il.ret(il.reg(4, 'lr')))
        return 4

BlxLrOverride(Architecture['armv7']).register()
