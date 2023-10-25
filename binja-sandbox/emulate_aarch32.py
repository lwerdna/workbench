#!/usr/bin/env python

sz_lookup = {1:'.b', 2:'.w', 4:'.d', 8:'.q', 16:'.o'}
sz_lookup_py = {1:'_b', 2:'_w', 4:'_d', 8:'_q', 16:'_o'}

import os
import sys
import binascii

from unicorn import *
from unicorn.arm_const import *

import binaryninja
from binaryninja import core
from binaryninja import binaryview
from binaryninja import lowlevelil
from binaryninja.enums import LowLevelILOperation

CODE_MEM_START = 0
CODE_MEM_LENGTH = 2**16
STACK_MEM_START = 0xFFFF0000
STACK_MEM_LENGTH = 2**16  

reg_name_to_uc_id = {
    'r0': UC_ARM_REG_R0, 'r1': UC_ARM_REG_R1, 'r2': UC_ARM_REG_R2, 'r3': UC_ARM_REG_R3,
    'r4': UC_ARM_REG_R4, 'r5': UC_ARM_REG_R5, 'r6': UC_ARM_REG_R6, 'r7': UC_ARM_REG_R7,
    'r8': UC_ARM_REG_R8, 'r9': UC_ARM_REG_R9, 'r10': UC_ARM_REG_R10, 'r11': UC_ARM_REG_R11,
    'ip': UC_ARM_REG_R12, 'sp': UC_ARM_REG_SP, 'lr': UC_ARM_REG_LR, 'pc': UC_ARM_REG_PC,
    'cpsr': UC_ARM_REG_CPSR,
}

def spawn_vm():
    # set up unicorn instance
    uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)
    uc.mem_map(CODE_MEM_START, CODE_MEM_LENGTH)
    uc.mem_map(STACK_MEM_START, STACK_MEM_LENGTH)
    uc.reg_write(reg_name_to_uc_id['pc'], CODE_MEM_START)
    uc.reg_write(reg_name_to_uc_id['sp'], STACK_MEM_START + STACK_MEM_LENGTH)
    return uc

def emulate_instr():
    if not hasattr(instr, 'operation'):
        return operand_to_expr(instr)

def get_bits(value, hi, lo=None):
    if lo == None:
        lo = hi
    width = hi - lo + 1
    mask = (1<<(hi+1))-1
    return (value & mask) >> lo

def decompose_cpsr(cpsr):
    N = get_bits(cpsr, 31)
    Z = get_bits(cpsr, 30)
    C = get_bits(cpsr, 29)
    V = get_bits(cpsr, 28)

    IT = (get_bits(cpsr, 15, 10) << 2) | get_bits(cpsr, 26, 25)
    J = get_bits(cpsr, 24)
    reserved = get_bits(cpsr, 23, 20)
    GE = get_bits(cpsr, 19, 16)

    E = get_bits(cpsr, 9)
    A = get_bits(cpsr, 8)
    I = get_bits(cpsr, 7)
    F = get_bits(cpsr, 6)
    T = get_bits(cpsr, 5)
    M = get_bits(cpsr, 4, 0)

    return {'N':N, 'Z':Z, 'C':C, 'V':V, 'IT':IT, 'J':J, 'reserved':reserved, 'GE':GE,
            'E':E, 'A':A, 'I':I, 'F':F, 'T':T, 'M':M}

def show_context(uc):
    reg_ids = [
        UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
        UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
        UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11,
        UC_ARM_REG_R12, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC,
        UC_ARM_REG_CPSR,
    ]

    regs = [uc.reg_read(x) for x in reg_ids]
    regs_str = ['%08X' % x for x in regs]
    regs_str = [x for (i,x) in enumerate(regs_str)]

    # special handling of nzcv
    info = decompose_cpsr(uc.reg_read(UC_ARM_REG_CPSR))
    n,z,c,v,t = (info.get(x) for x in 'NZCVT')

    # show context
    print(' r0=%s  r1=%s  r2=%s  r3=%s' % (regs_str[0], regs_str[1], regs_str[2], regs_str[3]))
    print(' r4=%s  r5=%s  r6=%s  r7=%s' % (regs_str[4], regs_str[5], regs_str[6], regs_str[7]))
    print(' r8=%s  r9=%s r10=%s r11=%s' % (regs_str[8], regs_str[9], regs_str[10], regs_str[11]))
    print(' ip=%s  sp=%s  lr=%s  pc=%s' % (regs_str[12], regs_str[13], regs_str[14], regs_str[15]))
    print(' cpsr=%s (N=%d Z=%d C=%d V=%d T=%d)' % (regs_str[16], n, z, c, v, t))

#    addr = regs[15]
#    data = uc.mem_read(addr, 4)
#    disfunc = cs_thumb.disasm if is_thumb(uc) else cs_arm.disasm
#    for i in disfunc(data, addr):
#        bytes_str = ' '.join(['%02X'%b for b in i.bytes]).ljust(2+1+2+1+2+1+2)
#        print(f'{i.address:08X}: {bytes_str} {i.mnemonic} {i.op_str}')
#        break

def operand_to_expr(operand):
    if isinstance(operand, lowlevelil.ILRegister):
        # shouldn't happen! ILRegister *denotes* a register, doesn't *read* a register
        breakpoint()
    elif isinstance(operand, binaryninja.variable.ConstantRegisterValue):
        return operand.value
    else:
        breakpoint()

def emulate_llil_instruction(uc, instr):
    if not hasattr(instr, 'operation'):
        return operand_to_expr(instr)

    if instr.operation == LowLevelILOperation.LLIL_SET_REG:
        arg0, arg1 = instr.operands
        assert isinstance(arg0, lowlevelil.ILRegister)
        uc_reg_id = reg_name_to_uc_id[arg0.name]
        uc.reg_write(uc_reg_id, emulate_llil_instruction(uc, arg1))

    elif instr.operation == LowLevelILOperation.LLIL_CONST:
        return operand_to_expr(instr.value)

    elif instr.operation == LowLevelILOperation.LLIL_REG:
        arg0 = instr.operands[0]
        assert isinstance(arg0, lowlevelil.ILRegister)
        return uc.reg_read(reg_name_to_uc_id[arg0.name])

    else:
        breakpoint()

if __name__ == '__main__':
    from helpers import *

    uc = spawn_vm()
    show_context(uc)

    print('emulating: mov r0, #0xDEAD')
    llil = lift_bytes('armv7', b'\xad\x0e\x0d\xe3')
    print('\n'.join(il_to_text_line(x) for x in llil))
    emulate_llil_instruction(uc, llil[0])

    show_context(uc)

    print('emulating: mov r2, r0')
    llil = lift_bytes('armv7', b'\x00\x20\xa0\xe1')
    print('\n'.join(il_to_text_line(x) for x in llil))
    emulate_llil_instruction(uc, llil[0])

    show_context(uc)


