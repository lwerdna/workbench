from binaryninja.enums import *
from binaryninja import lowlevelil

from MemoryArrayU8 import *

llil_cmp_ops = { LowLevelILOperation.LLIL_CMP_E,
                 LowLevelILOperation.LLIL_CMP_NE,
                 LowLevelILOperation.LLIL_CMP_SGE,
                 LowLevelILOperation.LLIL_CMP_SGT,
                 LowLevelILOperation.LLIL_CMP_SLT,
                 LowLevelILOperation.LLIL_CMP_SLE,
                 LowLevelILOperation.LLIL_CMP_UGE }

class State():
    def __init__(self, arch, initialize_memory=True):
        # eg:
        # 'rax#0' : BitVec('rax#0', 64)
        self.var_refs = {}
        self.conjuncts = []

        self.arch = arch
        self.stack_reg = arch.stack_pointer

        assert arch.regs[arch.stack_pointer].size == arch.address_size

        self.mem = MemoryArrayU8(arch.address_size * 8)

    def constrain(self, expr):
        if type(expr) == str:
            expr = constraint_string_to_z3(expr, self)

        self.conjuncts.append(expr)

    # retrieve the z3 variable reference for a register, PLUS:
    #   - creating it if needed
    #   - adding subregister constraints if needed
    #
    # eg:
    #     get_reg_var('rax', 0) -> BitVec('rax#0', 64)
    #     get_reg_var('rax', 1) -> BitVec('rax#1', 64)
    #     get_reg_var('al', 2)  -> BitVec('al#2', 8)
    #       - adding constraint: al#2 = Extract(7, 0, #rax2)
    #     get_reg_var('al', 2)  -> existing reference to al#2
    #       - adding nothing, since we remember already creating this var/reg
    #
    def get_reg_var(self, reg_name, version=0):
        reg_info = self.arch.regs.get(reg_name, None)
        assert reg_info

        # is the register known?
        ssa_name = f'{reg_name}#{version}'
        if ssa_name in self.var_refs:
            return self.var_refs[ssa_name]

        # full-width registers get labeled by their name
        width = self.arch.regs[reg_name].size * 8
        if reg_info.full_width_reg == reg_name:
            var = z3.BitVec(ssa_name, width)
            self.var_refs[ssa_name] = var
            return var

        # partial-width registers like eax become Extract expressions from their full-width container
        fwexpr = self.get_reg_var(reg_info.full_width_reg, version)
        lsb = reg_info.offset * 8
        msb = lsb + reg_info.size * 8 - 1
        var = z3.BitVec(ssa_name, width)
        self.var_refs[ssa_name] = var
        self.conjuncts.append(var == z3.Extract(msb, lsb, fwexpr))
        return var

    def get_ssa_reg_var(self, ssa_reg):
        return self.get_reg_var(ssa_reg.reg.name, ssa_reg.version)

    def get_ssa_flag_var(self, ssa_flag):
        assert type(ssa_flag.flag) == binaryninja.lowlevelil.ILFlag
        ssa_name = f'{ssa_flag.flag.name}#{ssa_flag.version}'
        if not ssa_name in self.var_refs:
            #self.var_refs[ssa_name] = z3.BitVec(ssa_name, 1)
            self.var_refs[ssa_name] = z3.Bool(ssa_name)
        return self.var_refs[ssa_name]

    def stack_var_name(self, bias):
        expr = z3.simplify(self.get_reg_var(self.stack_reg) + bias)
        return 'mem[%s]' % pretty_print_z3(expr)

    def operand_to_expr(self, oper):
        #assert isinstance(oper, LowLevelILOperand)

        #if isinstance(oper, lowlevelil.ILRegister):
        if isinstance(oper, lowlevelil.SSARegister):
            return self.get_ssa_reg_var(oper)
        elif isinstance(oper, lowlevelil.LowLevelILConst):
            value = oper.value
            if type(value) == int:
                return z3.BitVecVal(value, 8*oper.size)
            elif isinstance(value, binaryninja.variable.ConstantRegisterValue):
                return z3.BitVecVal(value.value, 8*oper.size)
            else:
                #breakpoint()
                assert False
        elif isinstance(oper, lowlevelil.SSAFlag):
            return self.get_ssa_flag_var(oper)
        else:
            print('operand_to_expr() unsupported: ' + str(oper))
            breakpoint()
            assert False

    # LLIL instruction to z3 expression
    def llil_to_expr(self, instr):
        # maybe it's
        if not hasattr(instr, 'operation'):
            return self.operand_to_expr(instr)

        #if loglevel > 0:
        #    print(f'State.llil_to_expr({str(instr)})')

        # comparisons
        if instr.operation in llil_cmp_ops:
            lhs = self.llil_to_expr(instr.operands[0])
            rhs = self.llil_to_expr(instr.operands[1])

            if instr.operation == LowLevelILOperation.LLIL_CMP_E:
                return lhs == rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_NE:
                return lhs != rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_SGE:
                return lhs >= rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_SGT:
                return lhs > rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_SLT:
                return lhs < rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_SLE:
                return lhs <= rhs
            elif instr.operation == LowLevelILOperation.LLIL_CMP_UGE:
                return z3.UGE(lhs, rhs)
            assert False

        # arithmetic
        if instr.operation == LowLevelILOperation.LLIL_ADD:
            return z3.simplify(
                self.llil_to_expr(instr.operands[0]) + self.llil_to_expr(instr.operands[1])
            )

        elif instr.operation == LowLevelILOperation.LLIL_SUB:
            return z3.simplify(
                self.llil_to_expr(instr.operands[0]) - self.llil_to_expr(instr.operands[1])
            )

        # bit operations
        elif instr.operation == LowLevelILOperation.LLIL_LSL:
            return self.llil_to_expr(instr.operands[0]) << \
                self.llil_to_expr(instr.operands[1])

        elif instr.operation == LowLevelILOperation.LLIL_LSR:
            return z3.LShR(
                self.llil_to_expr(instr.operands[0]),
                self.llil_to_expr(instr.operands[1])
            )

        elif instr.operation == LowLevelILOperation.LLIL_XOR:
            return self.llil_to_expr(instr.operands[0]) ^ \
                self.llil_to_expr(instr.operands[1])

        elif instr.operation == LowLevelILOperation.LLIL_CONST or \
             instr.operation == LowLevelILOperation.LLIL_CONST_PTR:
            return z3.BitVecVal(instr.operands[0], instr.size * 8)

        # bitwise complement, not logical
        elif instr.operation == LowLevelILOperation.LLIL_NOT:
            return ~self.operand_to_expr(instr.operands[0])

        #elif instr.operation == LowLevelILOperation.LLIL_LOAD:
        elif instr.operation == LowLevelILOperation.LLIL_LOAD_SSA:
            addr = self.llil_to_expr(instr.operands[0])
            # instr.operands[1] is the memory version
            # we ignore this in favor of our own memory tracking
            return self.mem.read(addr, instr.size * 8)

        # POP is exceptional, because it both returns a value _AND_ has a side effect (updated stack pointer)
        elif instr.operation == LowLevelILOperation.LLIL_POP:
            addr = self.var_refs[self.stack_reg]
            result = self.mem.read(addr, instr.size * 8)
            # TODO: adjust stack reg by default reg width instead of hardcoded 8
            self.var_refs[self.stack_reg] = self.var_refs[self.stack_reg] + 8
            return result

        #elif instr.operation == LowLevelILOperation.LLIL_REG:
        elif instr.operation == LowLevelILOperation.LLIL_REG_SSA:
            return self.operand_to_expr(instr.src)

        elif instr.operation == LowLevelILOperation.LLIL_REG_SSA_PARTIAL:
            parent = instr.operands[0]
            child = instr.operands[1]
            return self.get_reg_var(child.name, parent.version)

        elif instr.operation == LowLevelILOperation.LLIL_ZX:
            result = self.llil_to_expr(instr.src)
            if instr.size > instr.src.size:
                width_diff = 8 * (instr.size - instr.src.size)
                head = z3.BitVecVal(0, width_diff)
                result = z3.Concat(head, result)
            return result

        elif instr.operation == LowLevelILOperation.LLIL_FLAG_SSA:
            return self.llil_to_expr(instr.operands[0])

        else:
            print(f'llil_to_expr() unsupported: {instr} at 0x{instr.address:X}')
            breakpoint()
            assert False
            #breakpoint()

    def execute(self, instr, phi_idx):
        #if loglevel > 0:
        #    print(f'State.execute({str(instr)})')

        if instr.operation == LowLevelILOperation.LLIL_POP:
            # TODO: adjust stack reg by default reg width instead of hardcoded 8
            self.var_refs[self.stack_reg] = z3.simplify(self.var_refs[self.stack_reg] + 8)

        elif instr.operation == LowLevelILOperation.LLIL_PUSH:
            assert False
            #breakpoint()
            # TODO: adjust stack reg by default reg width instead of hardcoded 8

            # rsp -= 8
            self.var_refs[self.stack_reg] = z3.simplify(self.var_refs[self.stack_reg] - 8)

            # write to stack
            addr = self.var_refs[self.stack_reg]
            val = self.llil_to_expr(instr.operands[0])
            self.mem.write(addr, val, instr.size * 8)

        # better named "LLIL_REG_READ"
        elif instr.operation == LowLevelILOperation.LLIL_REG:
            return self.operand_to_expr(instr.operands[0])

        elif instr.operation == LowLevelILOperation.LLIL_RET:
            pass

        #elif instr.operation == LowLevelILOperation.LLIL_SET_REG:
        elif instr.operation == LowLevelILOperation.LLIL_SET_REG_SSA or \
             instr.operation == LowLevelILOperation.LLIL_SET_REG_SSA_PARTIAL:

            lhs, rhs = None, None
            if instr.operation == LowLevelILOperation.LLIL_SET_REG_SSA:
                lhs = self.get_ssa_reg_var(instr.operands[0])
                rhs = self.llil_to_expr(instr.operands[1])
            else:
                parent = instr.operands[0]
                child = instr.operands[1]
                lhs = self.get_reg_var(child.name, parent.version)
                rhs = self.llil_to_expr(instr.operands[2])

            self.conjuncts.append(lhs == rhs)

        #elif instr.operation == LowLevelILOperation.LLIL_STORE:
        elif instr.operation == LowLevelILOperation.LLIL_STORE_SSA:
            addr = self.llil_to_expr(instr.operands[0])
            # operands[1] is destination memory version
            # operands[2] is source memory version
            value = self.llil_to_expr(instr.operands[3])
            self.mem.write(addr, value, instr.size * 8)

        elif instr.operation == LowLevelILOperation.LLIL_MEM_PHI:
            pass
        elif instr.operation == LowLevelILOperation.LLIL_REG_PHI:
            try:
                lhs = self.get_ssa_reg_var(instr.operands[0])
                rhs = self.get_ssa_reg_var(instr.operands[1][phi_idx])
                self.conjuncts.append(lhs == rhs)
            except Exception as e:
                breakpoint()
                pass

        elif instr.operation == LowLevelILOperation.LLIL_CALL_SSA:
            pass

        elif instr.operation == LowLevelILOperation.LLIL_SET_FLAG_SSA:
            # cond:0#1 = r0#13 == 0x50
            lhs = self.llil_to_expr(instr.operands[0])
            rhs = self.llil_to_expr(instr.operands[1])
            self.conjuncts.append(lhs == rhs)

        else:
            print(f'state.execute() unsupported: {instr} at 0x{instr.address}')
            print(' instr.operation: ' + str(instr.operation))

    def evaluate(self, var_name):
        expr = self.var_refs[var_name]
        assert z3.is_int_value(expr) or z3.is_bv_value(Expr)
        return expr.as_long()

