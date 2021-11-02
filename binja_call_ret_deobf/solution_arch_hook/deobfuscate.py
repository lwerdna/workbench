from binaryninja.architecture import Architecture, ArchitectureHook
from binaryninja.function import InstructionTextToken, InstructionInfo
from binaryninja.enums import InstructionTextTokenType, BranchType

class X86DeobfuscateHook(ArchitectureHook):
    # test whether the data qualifies for the push/ret deobfuscation
    # return (destination, length) if it qualifies
    # return None if it doesn't
    def qualifies(self, data, addr):
        arch = super(X86DeobfuscateHook, self)
        toks_a, len_a = arch.get_instruction_text(data, addr)
        if not toks_a:
            return None

        if toks_a[0].text == 'push':
            toks_b, len_b = arch.get_instruction_text(data[len_a:], addr+len_a)

            if toks_b[0].text in ['ret', 'retn']:
                tok_dest = toks_a[-1]
                assert tok_dest.text.startswith('0x')
                return (int(tok_dest.text, 16), len_a + len_b)

        return None

    def get_instruction_text(self, data, addr):
        tmp = self.qualifies(data, addr)
        if not tmp:
            return super(X86DeobfuscateHook, self).get_instruction_text(data, addr)

        (push_addr, length) = tmp
        print('%08X: push+ret found, disassembling as jmp to 0x%X' % (addr, push_addr))

        tok_jmp = InstructionTextToken(InstructionTextTokenType.InstructionToken, "jmp")
        tok_space = InstructionTextToken(InstructionTextTokenType.TextToken, '     ')
        tok_dest = InstructionTextToken(InstructionTextTokenType.PossibleAddressToken, hex(push_addr), push_addr)
        return [tok_jmp, tok_space, tok_dest], length

    def get_instruction_info(self, data, addr):
        tmp = self.qualifies(data, addr)
        if not tmp:
            return super(X86DeobfuscateHook, self).get_instruction_info(data, addr)

        (push_addr, length) = tmp
        print('%08X: push+ret found, informing binja of unconditional branch to 0x%X' % (addr, push_addr))

        result = InstructionInfo()
        result.length = length
        result.add_branch(BranchType.UnconditionalBranch, push_addr)
        return result

# Install the hook by constructing it with the desired architecture to hook, then registering it
X86DeobfuscateHook(Architecture['x86']).register()
