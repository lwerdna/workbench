#!/usr/bin/env python
# an assembly REPL for aarch32 execution environment (A32/T32 instruction sets)

import re
import struct
import readline

from unicorn import *
from unicorn.arm_const import *

from keystone import *
from capstone import *

from termcolor import colored

from aarch32 import *
from helpers import *

CODE_MEM_START = 0
CODE_MEM_LENGTH = 2**16
STACK_MEM_START = 0xFFFF0000
STACK_MEM_LENGTH = 2**16

# set up emulator, assembler
ks_arm = Ks(KS_ARCH_ARM, KS_MODE_ARM + KS_MODE_LITTLE_ENDIAN)
ks_thumb = Ks(KS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)
cs_arm = Cs(CS_ARCH_ARM, CS_MODE_ARM + CS_MODE_LITTLE_ENDIAN)
cs_thumb = Cs(CS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)

uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

uc.mem_map(CODE_MEM_START, CODE_MEM_LENGTH)
uc.mem_map(STACK_MEM_START, STACK_MEM_LENGTH)
uc.reg_write(reg_name_to_uc_id['pc'], CODE_MEM_START)
uc.reg_write(reg_name_to_uc_id['sp'], STACK_MEM_START + STACK_MEM_LENGTH)

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

def step(count=1, stop_addr=0x100000000):
    global uc
    thumb = bool(uc.reg_read(UC_ARM_REG_CPSR) & 0x20)
    pointer = uc.reg_read(UC_ARM_REG_PC)
    if thumb and (pointer & 0) == 0:
        pointer += 1
    #print('starting emulation at pointer: 0x%08X' % pointer)
    uc.emu_start(pointer, stop_addr, timeout=0, count=count)

while 1:
    do_show_context = False

    pc = uc.reg_read(UC_ARM_REG_PC)
    cs = cs_thumb if is_thumb(uc) else cs_arm

    cmd = input('> ')

    try:
        if cmd.startswith(';') or cmd=='' or cmd.isspace():
            pass

        # is this a general (platform-independent) command?
        result = general_handle_command(cmd, uc, cs, pc, reg_name_to_uc_id)
        match result:
            case 'quit':
                break
            case 'executed':
                show_context(uc)
                continue
            case True:
                continue

        # basic execution
        if m := re.match(r'go?(\d+)', cmd): # go
            stop_addr = int(m.group(1), 16)
            print(colored(f'emulating until 0x{stop_addr:X}', 'yellow'))
            step(count=0, stop_addr=stop_addr)
            do_show_context = True

        elif cmd == 't': # step into
            step()
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
            step()
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
