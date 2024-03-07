#!/usr/bin/env python

import os, sys, re
import readline

# capstone, keystone, unicorn
from capstone import *
from keystone import *
from unicorn import *
from unicorn.x86_const import *

from termcolor import colored

from helpers import *

STACK_ADDR = 0xF0000000
STACK_LENGTH = 0x00020000

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

# set up a page at 0
mu.mem_map(0, 4096)
# set up the stack
print(f'Setting up stack at [0x{STACK_ADDR:08X}, 0x{STACK_ADDR+STACK_LENGTH:08X})')
mu.mem_map(STACK_ADDR, STACK_LENGTH)
mu.reg_write(UC_X86_REG_RSP, STACK_ADDR+STACK_LENGTH//2)

regs_old = [-1]*len(rname_to_unicorn)
def show_context():
    global mu
    global regs_old

    rip = mu.reg_read(UC_X86_REG_RIP)

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
        (rip, mu.reg_read(UC_X86_REG_EFLAGS)))

    data_rip = mu.mem_read(rip, 16)
    for i in cs.disasm(data_rip, rip):
        bstring = ''.join(['%02X'%k for k in i.bytes])
        print("%016X: %s %s %s" % (i.address, bstring, i.mnemonic, i.op_str))
        break

def step(count=1):
    global mu
    pointer = mu.reg_read(UC_X86_REG_RIP)
    print('starting emulation at pointer: 0x%08X' % pointer)
    mu.emu_start(pointer, 0xFFFFFFFF, timeout=0, count=1)

if __name__ == '__main__':
    if sys.argv[1:]:
        fpath = sys.argv[1]
        import binaryninja
        print('analyzing %s' % fpath)
        with binaryninja.open_view(fpath) as bv:
            for seg in bv.segments:
                alloc_len = max(4096, len(seg))
                #prot = UC_PROT_NONE
                prot = UC_PROT_READ
                if seg.readable:
                    prot |= UC_PROT_READ
                if seg.writable:
                    prot |= UC_PROT_WRITE
                if seg.executable:
                    prot |= UC_PROT_EXEC
                print('mapping segment [%X, %X)' % (seg.start, seg.end))
                mu.mem_map(seg.start, alloc_len, prot)
                mu.mem_write(seg.start, bv.read(seg.start, len(seg)))
        print('setting rip to %X' % bv.entry_point)
        mu.reg_write(UC_X86_REG_RIP, bv.entry_point)

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
            elif cmd == 'u' or re.match(r'u (.*)', cmd):
                addr = mu.reg_read(UC_X86_REG_RIP) if cmd == 'u' else int(cmd[2:], 16)
                data = mu.mem_read(addr, 64)
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

            # quit
            elif cmd == 'q':
                break

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



