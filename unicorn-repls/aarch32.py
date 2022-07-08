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

from helpers import *

rname_to_unicorn = {
    'r0': UC_ARM_REG_R0, 'r1': UC_ARM_REG_R1, 'r2': UC_ARM_REG_R2, 'r3': UC_ARM_REG_R3,
    'r4': UC_ARM_REG_R4, 'r5': UC_ARM_REG_R5, 'r6': UC_ARM_REG_R6, 'r7': UC_ARM_REG_R7,
    'r8': UC_ARM_REG_R8, 'r9': UC_ARM_REG_R9, 'r10': UC_ARM_REG_R10, 'r11': UC_ARM_REG_R11,
    'ip': UC_ARM_REG_R12, 'sp': UC_ARM_REG_SP, 'lr': UC_ARM_REG_LR, 'pc': UC_ARM_REG_PC,
    'cpsr': UC_ARM_REG_CPSR,
}

# set up emulator, assembler
ks_arm = Ks(KS_ARCH_ARM, KS_MODE_ARM + KS_MODE_LITTLE_ENDIAN)
ks_thumb = Ks(KS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)
cs_arm = Cs(CS_ARCH_ARM, CS_MODE_ARM + CS_MODE_LITTLE_ENDIAN)
cs_thumb = Cs(CS_ARCH_ARM, KS_MODE_THUMB + KS_MODE_LITTLE_ENDIAN)
mu = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)
mu.mem_map(0, 4096)

# track context

regs_old = [-1]*len(rname_to_unicorn)
def show_context():
    global mu
    global regs_old

    reg_ids = [
        UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
        UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
        UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11,
        UC_ARM_REG_R12, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC,
        UC_ARM_REG_CPSR,
    ]

    regs = [mu.reg_read(x) for x in reg_ids]
    regs_str = ['%08X' % x for x in regs]
    regs_str = [x if regs[i]==regs_old[i] else colored(x, 'red') for (i,x) in enumerate(regs_str)]

    # special handling of nzcv
    cpsr = regs[16]
    (n,z,c,v,q,t) = (bool(cpsr & 0x80000000), bool(cpsr & 0x40000000),
        bool(cpsr & 0x20000000), bool(cpsr & 0x10000000), bool(cpsr & 0x8000000),
        bool(cpsr & 0x20))

    # show context
    print(' r0=%s  r1=%s  r2=%s  r3=%s' % (regs_str[0], regs_str[1], regs_str[2], regs_str[3]))
    print(' r4=%s  r5=%s  r6=%s  r7=%s' % (regs_str[4], regs_str[5], regs_str[6], regs_str[7]))
    print(' r8=%s  r9=%s r10=%s r11=%s' % (regs_str[8], regs_str[9], regs_str[10], regs_str[11]))
    print(' ip=%s  sp=%s  lr=%s  pc=%s' % (regs_str[12], regs_str[13], regs_str[14], regs_str[15]))
    print(' cpsr=%s (N=%d Z=%d C=%d V=%d T=%d)' % (regs_str[16], n, z, c, v, t))

    regs_old = regs

    addr = regs[15]
    data = mu.mem_read(addr, 4)
    disfunc = cs_thumb.disasm if thumb else cs_arm.disasm
    for i in disfunc(data, addr):
        bytes_str = ' '.join(['%02X'%b for b in i.bytes]).ljust(2+1+2+1+2+1+2)
        print(f'0x{i.address:08X}: {bytes_str} {i.mnemonic} {i.op_str}')
        break

def step(count=1):
    global mu
    thumb = bool(mu.reg_read(UC_ARM_REG_CPSR) & 0x20)
    pointer = mu.reg_read(UC_ARM_REG_PC)
    if thumb and (pointer & 1) == 0:
        pointer += 1
    print('starting emulation at pointer: 0x%08X' % pointer)
    mu.emu_start(pointer, 0x100000000, timeout=0, count=1)

while 1:
    do_show_context = False

    pc = mu.reg_read(UC_ARM_REG_PC)
    thumb = bool(mu.reg_read(UC_ARM_REG_CPSR) & 0x20)

    cmd = input('> ')

    try:
        # show context
        if cmd == 'r':
            do_show_context = True

        # reg write, example:
        # r3 = 0xDEADBEEF
        elif m := re.match(r'([^\s]+)\s*=\s*(.+)', cmd):
            (rname, rval) = m.group(1, 2)
            if rname in rname_to_unicorn:
                mu.reg_write(rname_to_unicorn[rname], int(rval, 16))

                # unicorn initialized to arm will fall back to arm automatically after
                # register set, so compensate for this
                if thumb:
                    mu.reg_write(UC_ARM_REG_CPSR, mu.reg_read(UC_ARM_REG_CPSR) | 0x20)

                do_show_context = True
            else:
                print('ERROR: unknown register %s' % rname)

        # dump bytes, example:
        # db 0
        elif m := re.match(r'db (.*)', cmd):
            addr = int(m.group(1),16)
            data = mu.mem_read(addr, 64)
            print(get_hex_dump(data, addr))

        # disassemble bytes, example:
        # u 0
        elif m := re.match(r'u (.*)', cmd):
            addr = int(m.group(1),16)
            data = mu.mem_read(addr, 64)
            disfunc = cs_thumb.disasm if thumb else cs_arm.disasm
            for i in disfunc(data, addr):
                addr_str = '0x%08X' % i.address
                bytes_str = ' '.join(['%02X'%b for b in i.bytes]).ljust(2+1+2+1+2+1+2)
                print(f'{addr_str}: {bytes_str} {i.mnemonic} {i.op_str}')

        # enter bytes, example:
        # eb 0 AA BB CC DD
        elif m := re.match(r'eb ([a-fA-F0-9x]+) (.*)', cmd):
            (addr, bytestr) = m.group(1, 2)
            addr = int(addr, 16)
            data = b''.join([int(x, 16).to_bytes(1,'big') for x in bytestr.split()])
            print('writing:', colored(data.hex(), 'green'))
            mu.mem_write(addr, data)

        elif m := re.match(r'go?(\d+)', cmd):
            mu.emu_start(pc, 0x100000000, timeout=0, count=int(m.group(1)))

        # step into, example:
        # t
        elif cmd == 't':
            step()
            do_show_context = True

        # toggle arm/thumb mode
        elif cmd == 'mode':
            mu.reg_write(UC_ARM_REG_CPSR, mu.reg_read(UC_ARM_REG_CPSR) ^ (0x20))
            do_show_context = True

        # assemble, step, example:
        # mov r0, 0xDEAD
        elif cmd:
            # assume the input is assembler and place it at current PC
            asmstr = cmd
            encoding, count = None, None

            if thumb:
                encoding, count = ks_thumb.asm(asmstr, addr=pc)
            else:
                encoding, count = ks_arm.asm(asmstr, addr=pc)

            data = b''.join([x.to_bytes(1, 'big') for x in encoding])

            print('%s-assembled %08X:' % ('thumb' if thumb else 'arm', pc), colored(data.hex(), 'green'), ' (%d bytes)'%len(encoding))
            mu.mem_write(pc, data)
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
        show_context()
