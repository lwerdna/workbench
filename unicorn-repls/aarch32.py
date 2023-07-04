#!/usr/bin/env python

# support lib for aarch32

import struct

from unicorn import *
from unicorn.arm_const import *

from capstone import *

from termcolor import colored

from helpers import get_bits

reg_name_to_uc_id = {
    'r0': UC_ARM_REG_R0, 'r1': UC_ARM_REG_R1, 'r2': UC_ARM_REG_R2, 'r3': UC_ARM_REG_R3,
    'r4': UC_ARM_REG_R4, 'r5': UC_ARM_REG_R5, 'r6': UC_ARM_REG_R6, 'r7': UC_ARM_REG_R7,
    'r8': UC_ARM_REG_R8, 'r9': UC_ARM_REG_R9, 'r10': UC_ARM_REG_R10, 'r11': UC_ARM_REG_R11,
    'ip': UC_ARM_REG_R12, 'sp': UC_ARM_REG_SP, 'lr': UC_ARM_REG_LR, 'pc': UC_ARM_REG_PC,
    'cpsr': UC_ARM_REG_CPSR,
}

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

def is_cond_met(cond, apsr):
    N = apsr & 0x80000000
    Z = apsr & 0x40000000
    C = apsr & 0x20000000
    V = apsr & 0x10000000

    match cond:
        case 0b0000: # EQ    equal
            return Z
        case 0b0001: # NE    not equal
            return not Z
        case 0b0010: # CS/HS unsigned higher or same
            return C
        case 0b0011: # CC/LO unsigned lower
            return not C
        case 0b0100: # MI    negative
            return N
        case 0b0101: # PL    positive or zero
            return not N
        case 0b0110: # VS    overflow
            return V
        case 0b0111: # VC    no overflow
            return not V
        case 0b1000: # HI    unsigned higher
            return C and not Z
        case 0b1001: # LS    unsigned lower or same
            return not C and Z
        case 0b1010: # GE    greater or equal
            return N == V
        case 0b1011: # LT    less than
            return N != V
        case 0b1100: # GT    greater than
            return not Z and N == V
        case 0b1101: # LE    less than or equal
            return Z or (N != V)
        case 0b1110: # AL    always
            return True
        case 0b1111: # ?
            return None

#----------------------------------------------------------------------
# instructions
#----------------------------------------------------------------------

def is_call(uc, i):
    return i.id in [ARM_INS_BL, ARM_INS_BLX]

def is_return(uc, i):
    apsr = uc.reg_read(UC_ARM_REG_CPSR)

    if len(i.bytes) == 2:
        sz = 2
        insword, = struct.unpack('<H', i.bytes)
    else:
        sz = 4
        if is_thumb(uc):
            h0, h1 = struct.unpack('<HH', i.bytes)
            insword = (h0 << 16) | h1
        else:
            insword, = struct.unpack('<I', i.bytes)

    # RETURN METHOD: POP TO PC
    #
    # (pdb) i
    # <CsInsn 0xfabc [10bd]: pop {r4, pc}>
    # (pdb) i.regs_write()
    # *** capstone.CsError: Details are unavailable (CS_ERR_DETAIL)
    # (pdb) i.reg_write(ARM_REG_PC)
    # *** capstone.CsError: Details are unavailable (CS_ERR_DETAIL)
    # so we have to do this manually...
    if i.id == ARM_INS_POP:
        # 16-bit encodings
        if sz == 2:
            # encoding T1
            if (insword & 0xFE00) == 0xBC00:
                return insword & 0x0100
            else:
                breakpoint()
                pass
        # 32-bit encodings
        else:
            # encoding A1
            if (insword & 0x0FFF0000) == 0x08BD0000:
                cond = insword >> 28
                if is_cond_met(cond, apsr):
                    return insword & 0x8000
                return False
            # encoding T2 (looks the same to me)
            if (insword & 0xFFFF0000) == 0xE8BD0000:
                return insword & 0x8000

            return False

    elif i.id == ARM_INS_BX:
        # 16-bit encodings
        if sz == 2:
            # T1
            assert insword & 0xFF80 == 0x4700, breakpoint()
            Rm = (insword & 0x78) >> 3
            return Rm == 14 # LR
        else:
            # A1
            assert insword & 0x0FFFFFF0 == 0x012FFF10, breakpoint()
            Rm = insword & 0xF
            return Rm == 14 # Lr

    return False

#----------------------------------------------------------------------
# execution state
#----------------------------------------------------------------------

def is_thumb(uc):
    return bool(uc.reg_read(UC_ARM_REG_CPSR) & 0x20)

def set_thumb(uc):
    uc.reg_write(UC_ARM_REG_CPSR, uc.reg_read(UC_ARM_REG_CPSR) | 0x20) # set T bit

def is_arm(uc):
    return not bool(uc.reg_read(UC_ARM_REG_CPSR) & 0x20)

def set_arm(uc):
    uc.reg_write(UC_ARM_REG_CPSR, uc.reg_read(UC_ARM_REG_CPSR) & 0xFFFFFFDF) # clear T bit

def get_pc(uc):
    return uc.reg_read(UC_ARM_REG_PC)

def set_pc(uc, addr):
    # pc isn't actually odd in thumb state, this is a unicorn convention that keeps the
    # processor in thumb mode
    addr = addr | 1 if is_thumb(uc) else addr & 0xFFFFFFFE
    uc.reg_write(UC_ARM_REG_PC, addr)
    return addr

#----------------------------------------------------------------------
# memory functions
#----------------------------------------------------------------------

def push_dword(uc, value):
    sp = uc.reg_read(UC_ARM_REG_SP)
    uc.reg_write(UC_ARM_REG_SP, sp-4)
    uc.mem_write(sp-4, struct.pack('<I', value))
    return sp-4

def read_string(uc, addr, limit=2048):
    result = ''

    for i in range(limit):
        tmp = uc.mem_read(addr, 1)
        if tmp[0] == 0:
            break
        result += chr(tmp[0])
        addr += 1

    return result

