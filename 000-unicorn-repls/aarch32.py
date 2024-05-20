#!/usr/bin/env python

# support lib for aarch32

import re
import struct
import readline

# capstone, keystone, unicorn
from capstone import *
from keystone import *
from unicorn import *
from unicorn.arm_const import *

from termcolor import colored

from helpers import *

# set up assemblers, disassemblers
ks_arm = Ks(KS_ARCH_ARM, KS_MODE_ARM + KS_MODE_LITTLE_ENDIAN)
ks_thumb = Ks(KS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)
cs_arm = Cs(CS_ARCH_ARM, CS_MODE_ARM + CS_MODE_LITTLE_ENDIAN)
cs_thumb = Cs(CS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)

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

#----------------------------------------------------------------------
# repl helpers
#----------------------------------------------------------------------

# track context
regs_old = [-1]*len(reg_name_to_uc_id)
def show_context(uc):
    global regs_old

    reg_ids = [
        UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
        UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
        UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11,
        UC_ARM_REG_R12, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC,
        UC_ARM_REG_CPSR,
    ]

    regs = [uc.reg_read(x) for x in reg_ids]
    regs_str = ['%08X' % x for x in regs]
    regs_str = [x if regs[i]==regs_old[i] else colored(x, 'red') for (i,x) in enumerate(regs_str)]

    # special handling of nzcv
    info = decompose_cpsr(uc.reg_read(UC_ARM_REG_CPSR))
    n,z,c,v,t = (info.get(x) for x in 'NZCVT')

    # show context
    print(' r0=%s  r1=%s  r2=%s  r3=%s' % (regs_str[0], regs_str[1], regs_str[2], regs_str[3]))
    print(' r4=%s  r5=%s  r6=%s  r7=%s' % (regs_str[4], regs_str[5], regs_str[6], regs_str[7]))
    print(' r8=%s  r9=%s r10=%s r11=%s' % (regs_str[8], regs_str[9], regs_str[10], regs_str[11]))
    print(' ip=%s  sp=%s  lr=%s  pc=%s' % (regs_str[12], regs_str[13], regs_str[14], regs_str[15]))
    print(' cpsr=%s (N=%d Z=%d C=%d V=%d T=%d)' % (regs_str[16], n, z, c, v, t))

    regs_old = regs

    addr = regs[15]
    data = uc.mem_read(addr, 4)
    disfunc = cs_thumb.disasm if is_thumb(uc) else cs_arm.disasm
    for i in disfunc(data, addr):
        print(f'{i.address:08X}: {i.bytes.hex()} {i.mnemonic} {i.op_str}')
        break

# if count == 0:
#     execute any count, until stop address
# else
#     execute count instructions, ignore stop address
def step(uc, count=1, stop_addr=0x100000000):
    thumb = bool(uc.reg_read(UC_ARM_REG_CPSR) & 0x20)
    pointer = uc.reg_read(UC_ARM_REG_PC)
    if thumb and (pointer & 0) == 0:
        pointer += 1
    #print('starting emulation at pointer: 0x%08X' % pointer)
    uc.emu_start(pointer, stop_addr, timeout=0, count=count)

#------------------------------------------------------------------------------
#
#------------------------------------------------------------------------------

def hook_mem_fetch_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED FETCH FROM ADDRESS: 0x{address:X})')
    uc.emu_stop()
    return False

def hook_mem_write_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED WRITE: {size} bytes {hex(value)} to 0x{address:X}')
    uc.emu_stop()
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED WRITE: {size} bytes {hex(value)} to 0x{address:X}')
    return True

def hook_mem_read_unmapped(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} UNMAPPED READ: {size} bytes from 0x{address:X})')
    uc.emu_stop()
    return True

def hook_mem_fetch_prot(uc, access, address, size, value, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    print(f'{pc:08X} EXEC FROM NX MEM AT 0x{address:X}')
    uc.emu_stop()
    return True

def install_default_hooks(uc):
    result = {}

    # hook unmapped fetches
    result['MEM_FETCH_UNMAPPED'] = uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, hook_mem_fetch_unmapped)
    # hook unmapped writes
    result['MEM_WRITE_UNMAPPED'] = uc.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, hook_mem_write_unmapped)
    # hook unmapped reads
    result['MEM_READ_UNMAPPED'] = uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED, hook_mem_read_unmapped)
    # hook execute from nx memory
    result['MEM_FETCH_PROT'] = uc.hook_add(UC_HOOK_MEM_FETCH_PROT, hook_mem_fetch_prot)

    return result

def callback_breakpoint(uc, address, size, user_data):
    pc = uc.reg_read(UC_ARM_REG_PC)
    #print(f'{pc:08X} BREAKPOINT! {user_data}')
    print(f'{pc:08X} BREAKPOINT!')
    uc.emu_stop()
    return True

#------------------------------------------------------------------------------
#
#------------------------------------------------------------------------------

def bp_add_helper(uc, addr, breakpoints):
    if addr in breakpoints:
        return
    print(f'bp_add_helper(..., 0x{addr:X}, ...)')
    hookobj = uc.hook_add(UC_HOOK_CODE, callback_breakpoint, begin=addr, end=addr)
    breakpoints[addr] = hookobj

def bp_del_helper(uc, addr, breakpoints):
    hookobj = breakpoints.get(addr)
    if not hookobj:
        return
    uc.hook_del(hookobj)
    del breakpoints[addr]

def repl(uc, script_lines=[]):
    pending_code = []
    breakpoints = {} # address -> hook object

    while 1:
        for code in pending_code:
            code()
        pending_code = []

        do_show_context = False

        pc = uc.reg_read(UC_ARM_REG_PC)
        cs = cs_thumb if is_thumb(uc) else cs_arm

        if script_lines:
            cmd = script_lines.pop(0)
        else:
            cmd = input('> ')

        try:
            if cmd.startswith(';') or cmd=='' or cmd.isspace(): # comments
                pass
            elif cmd == 'q': # quit?
                break;
            elif cmd == 'r': # show context?
                do_show_context = True
            elif general_mem_read_commands(uc, cmd):
                continue
            elif general_mem_write_commands(uc, cmd):
                continue
            elif general_register_commands(uc, cmd, reg_name_to_uc_id):
                continue
            elif general_disassemble_commands(uc, cmd, pc, cs):
                continue
            elif general_monitor_commands(uc, cmd):
                continue

            # basic execution
            elif cmd == 'g':
                if hookobj := breakpoints.get(pc): # step over possible bp
                    bp_del_helper(uc, pc, breakpoints)
                    step(uc, count=1)
                    bp_add_helper(uc, pc, breakpoints)

                step(uc, count=0)
                do_show_context = True

            elif m := re.match(r'g (.*)', cmd):
                if hookobj := breakpoints.get(pc): # step over possible bp
                    bp_del_helper(uc, pc, breakpoints)
                    step(uc, count=1)
                    bp_add_helper(uc, pc, breakpoints)

                stop_addr = int(m.group(1), 16)
                print(colored(f'emulating until 0x{stop_addr:X}', 'yellow'))
                step(uc, count=0, stop_addr=stop_addr)
                do_show_context = True

            elif cmd == 't': # step into
                if pc in breakpoints:
                    bp_del_helper(uc, pc, breakpoints)
                    pending_code.append(lambda: bp_add_helper(uc, pc, breakpoints))

                step(uc)
                do_show_context = True

            # toggle arm/thumb mode
            elif cmd == 'mode':
                set_arm(uc) if is_thumb(uc) else set_thumb(uc)
                do_show_context = True
            elif cmd == 'mode arm':
                set_arm(uc)
                do_show_context = True
            elif cmd == 'mode thumb':
                set_thumb(uc)
                do_show_context = True

            # breakpoint commands
            elif m := re.match(r'bp (.*)$', cmd):
                addr = int(m.group(1), 16)
                if addr in breakpoints:
                    print(f'breakpoint already at 0x{addr:X}')
                else:
                    bp_add_helper(uc, addr, breakpoints)

            elif m := re.match(r'bc (.*)$', cmd):
                addr = int(m.group(1), 16)
                if addr in breakpoints:
                    bp_del_helper(uc, addr, breakpoints)
                else:
                    print('breakpoint at 0x{addr:X} not found')

            elif cmd == 'bl':
                for addr in breakpoints:
                    print(f'breakpoint at 0x{addr:X}')

            # assemble, step, example:
            # mov r0, 0xDEAD
            elif cmd:
                # assume the input is assembler and place it at current PC
                asmstr = cmd
                encoding, count = None, None

                if is_thumb(uc):
                    encoding, count = ks_thumb.asm(asmstr, addr=pc)
                else:
                    encoding, count = ks_arm.asm(asmstr, addr=pc)

                data = b''.join([x.to_bytes(1, 'big') for x in encoding])

                print('%s-assembled %08X:' % ('thumb' if is_thumb(uc) else 'arm', pc), colored(data.hex(), 'green'), ' (%d bytes)'%len(encoding))
                uc.mem_write(pc, data)
                step(uc)
                do_show_context = True

        except KsError as e:
            print('keystone error:', e)

        except UcError as e:
            #print(e)
            #print(type(e))
            #print(dir(e))
            #print(e.args)
            print('unicorn error:', e)

        if do_show_context:
            show_context(uc)
