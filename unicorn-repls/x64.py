#!/usr/bin/env python

import re
import readline

# capstone, keystone, unicorn
from capstone import *
from keystone import *
from unicorn import *
from unicorn.x86_const import *

from termcolor import colored

from helpers import *

rname_to_unicorn = {
    'rax': UC_X86_REG_RAX, 'rbx': UC_X86_REG_RBX, 'rcx': UC_X86_REG_RCX, 'rdx': UC_X86_REG_RDX,
    'rsp': UC_X86_REG_RSP, 'rbp': UC_X86_REG_RBP, 'rsi': UC_X86_REG_RSI, 'rdi': UC_X86_REG_RDI,
    'rip': UC_X86_REG_RIP, 'eflags': UC_X86_REG_EFLAGS,
    'cs': UC_X86_REG_CS, 'ss': UC_X86_REG_SS, 'ds': UC_X86_REG_DS, 'rs': UC_X86_REG_ES,
    'fs': UC_X86_REG_FS, 'gs': UC_X86_REG_GS
}

# capstone, keystone, unicorn
cs = Cs(CS_ARCH_X86, CS_MODE_64)
ks = Ks(KS_ARCH_X86, KS_MODE_64)
mu = Uc(UC_ARCH_X86, UC_MODE_64)
mu.mem_map(0, 4096)

regs_old = [-1]*len(rname_to_unicorn)
def show_context():
    global mu
    global regs_old

    # show context
    print('rax=%016X rbx=%016X rcx=%016X rdx=%016X' % \
        (mu.reg_read(UC_X86_REG_RAX), mu.reg_read(UC_X86_REG_RBX), \
        mu.reg_read(UC_X86_REG_RCX), mu.reg_read(UC_X86_REG_RDX)))
    print('rsp=%016X rbp=%016X rsi=%016X rdi=%016X' % \
        (mu.reg_read(UC_X86_REG_RSP), mu.reg_read(UC_X86_REG_RBP), 
        mu.reg_read(UC_X86_REG_RSI), mu.reg_read(UC_X86_REG_RDI)))
    print(' cs=%016X  ss=%016X' % \
        (mu.reg_read(UC_X86_REG_CS), mu.reg_read(UC_X86_REG_SS)))
    print(' ds=%016X  es=%016X' % \
        (mu.reg_read(UC_X86_REG_DS), mu.reg_read(UC_X86_REG_ES)))
    print(' fs=%016X  gs=%016X' % \
        (mu.reg_read(UC_X86_REG_FS), mu.reg_read(UC_X86_REG_GS)))
    print('rip=%016X eflags=%016X' % \
        (mu.reg_read(UC_X86_REG_RIP), mu.reg_read(UC_X86_REG_EFLAGS)))

def step(count=1):
    global mu
    pointer = mu.reg_read(UC_X86_REG_RIP)
    print('starting emulation at pointer: 0x%08X' % pointer)
    mu.emu_start(pointer, 0xFFFFFFFF, timeout=0, count=1)

while 1:
    do_show_context = True
    cmd = input('> ')

    try:
        # show context
        if cmd == 'r':
            pass

        # reg write, example:
        # r3 = 0xDEADBEEF
        elif m := re.match(r'([^\s]+)\s*=\s*(.+)', cmd):
            (rname, rval) = m.group(1, 2)
            if rname in rname_to_unicorn:
                mu.reg_write(rname_to_unicorn[rname], int(rval, 16))
            else:
                print('ERROR: unknown register %s' % rname)
            do_show_context = False

        # dump bytes, example:
        # db 0
        elif m := re.match(r'db (.*)', cmd):
            addr = int(m.group(1),16)
            data = mu.mem_read(addr, 64)
            print(get_hex_dump(data, addr))
            do_show_context = False

        # unassemble, example:
        # u 0xDEAD
        elif m := re.match(r'u (.*)', cmd):
            addr = int(m.group(1),16)
            data = mu.mem_read(addr, 64)
            offs = 0
            for i in cs.disasm(data, addr):
                bstring = (''.join(['%02X'%k for k in i.bytes])).ljust(24)
                print("%08X: %s %s %s" % (i.address, bstring, i.mnemonic, i.op_str))
            do_show_context = False

        # enter bytes, example:
        # eb 0 AA BB CC DD
        elif m := re.match(r'eb ([a-fA-F0-9x]) (.*)', cmd):
            (addr, bytestr) = m.group(1, 2)
            addr = int(addr, 16)
            data = b''.join([int(x, 16).to_bytes(1,'big') for x in bytestr.split()])
            print('writing:', colored(data.hex(), 'green'))
            mu.mem_write(addr, data)
            do_show_context = False

        elif m := re.match(r'go?(\d+)', cmd):
            rip = mu.reg_read(UC_X86_REG_RIP)
            mu.emu_start(rip, 0x100000000, timeout=0, count=int(m.group(1)))

        # step into, example:
        # t
        elif cmd == 't':
            step()

        # assemble, example:
        # mov r0, 0xDEAD
        elif cmd:
            # assume the input is assembler and place it at current RIP
            asmstr = cmd
            rip = mu.reg_read(UC_X86_REG_RIP)
            encoding, count = ks.asm(asmstr, addr=rip)
            data = b''.join([x.to_bytes(1, 'big') for x in encoding])
            print('assembled %08X: %s (%d bytes)' % (rip, colored(data.hex(), 'green'), len(encoding)))
            mu.mem_write(rip, data)
            step()

    except KsError as e:
        print('keystone error:', e)
    except UcError as e:
        print('unicorn error:', e)

    if do_show_context:
        show_context()



