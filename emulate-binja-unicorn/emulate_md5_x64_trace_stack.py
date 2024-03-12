#!/usr/bin/env python

import struct

import capstone

from unicorn import *
from unicorn.x86_const import *

from md5_x64_dump import *

from helpers import *

cs_context = None
def disasm(data, addr):
    global cs_context
    if cs_context == None:
        cs_context = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    gen = cs_context.disasm(data, addr)
    insn = next(gen)
    return f'{insn.mnemonic} {insn.op_str}', insn.size

def disasm_uc(uc):
    rip = uc.reg_read(UC_X86_REG_RIP)
    mcode = uc.mem_read(rip, 20)
    distxt, _ = disasm(mcode, rip)
    return f'{rip:X}: {distxt}'

def setup_machine():
    uc = Uc(UC_ARCH_X86, UC_MODE_64)

    # calculate code area
    seg_start = align_down_4k(min(f['address'] for f in functions))
    seg_end = align_up_4k(max(f['address'] + f['length'] for f in functions))
    print(f'creating code segment [0x{seg_start:X}, 0x{seg_end:X})')

    # create code area
    uc.mem_map(seg_start, seg_end-seg_start)
    for function in functions:
        print(f'writing 0x{function["length"]:X} bytes of {function["name"]} to 0x{function["address"]:X}')
        uc.mem_write(function["address"], b''.join(function['instructions']))

    # create stack area
    STACK_MEM_START  = 0xF0000000
    STACK_MEM_LENGTH = 2**16    
    print(f'creating stack segment [0x{STACK_MEM_START:X}, 0x{STACK_MEM_START+STACK_MEM_LENGTH:X})')
    uc.mem_map(STACK_MEM_START, STACK_MEM_LENGTH)
    uc.reg_write(UC_X86_REG_RSP, STACK_MEM_START + STACK_MEM_LENGTH - 8*32) # 32 pushes

    return uc

if __name__ == '__main__':
    name2addr = {f['name']: f['address'] for f in functions}

    uc = setup_machine()
    uc.mem_map(0, 4096) # so we can return to 0

    # static unsigned char PADDING[64] = {0x80, 0, 0, ..., 0}
    uc.mem_map(0x100008000, 0x100009000) # for _PADDING
    uc.mem_write(0x100008050, b'\x80')

    # create the md5 context
    p_context = x64_alloc_stack(uc, 128)
    print(f'MD5_CTX allocated to [0x{p_context:X}, 0x{p_context+128:X})')

    instrs = 0
    if 1:
        def callback_code(uc, address, size, user_data):
            global instrs
            instrs += 1
            #print(f'rip=0x{rip:X} rax=0x{rax:X} rcx=0x{rcx:X} rdx=0x{rdx:X} rdi=0x{rdi:X} rsi=0x{rsi:X}')

            #rip = uc.reg_read(UC_X86_REG_RIP)
            #if uc.mem_read(rip, 3) in [b'\x8B\x45\xEC', b'\x3B\x45\xE0']:
            print(f'{disasm_uc(uc)}')

        uc.hook_add(UC_HOOK_CODE, callback_code)

    if 1:
        #fp_reads = open('stack_reads.txt', 'w')
        #fp_writes = open('stack_writes.txt', 'w')
        def callback_mem_access(uc, access, address, size, value, user_data):
            # UC_MEM_READ = 16
            # UC_MEM_WRITE = 17
            # UC_MEM_FETCH = 18
            #global fp_reads
            #global fp_writes
#            global instrs
#            #if address == 0xF000FE40:
#            #    breakpoint()
#            if access == UC_MEM_WRITE: #17
#                #print(">>> Memory is being WRITE at 0x%x, data size = %u, data value = 0x%x" %(address, size, value))
#                #fp_writes.write(f'{instrs} 0x{address:X}\n')
#                #print(f'{instrs} 0x{address:X} (WRITE)')
#                pass
#            elif access == UC_MEM_FETCH: #18
#                print(f'{instrs} 0x{address:X} (FETCH)')
#            elif access == UC_MEM_READ: #16
#                #print(">>> Memory is being READ at 0x%x, data size = %u" %(address, size))
#                #fp_reads.write(f'{instrs} 0x{address:X}\n')
#                print(f'{instrs} 0x{address:X} (READ)')

            print(f'{disasm_uc(uc)} <-- accesses address 0x{address:X} with access={access}')

        uc.hook_add(UC_HOOK_MEM_READ, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_WRITE, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_FETCH, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_WRITE_PROT, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_READ_PROT, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_FETCH_PROT, callback_mem_access, None)
        uc.hook_add(UC_HOOK_MEM_READ_AFTER, callback_mem_access, None)

    print('calling MD5Init(&context)')
    uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
    x64_push_qword(uc, 0) # return address
    uc.emu_start(name2addr['_MD5Init'], 0)

    buf = x64_alloc_stack(uc, 64)
    print(f'input string allocated to buffer [0x{buf:X}, 0x{buf+64:X})')
    input_str = b'The quick brown fox jumps over the lazy dog'
    uc.mem_write(buf, input_str)

    print('calling MD5Update(&context, "The quick brown fox jumps over the lazy dog", 43)')
    uc.reg_write(UC_X86_REG_RDI, p_context) # RDI = arg0
    uc.reg_write(UC_X86_REG_RSI, buf) # RSI = arg1
    uc.reg_write(UC_X86_REG_RDX, len(input_str)) # RDX = arg2
    x64_push_qword(uc, 0) # return address
    uc.emu_start(name2addr['_MD5Update'], 0)
    x64_free_stack(uc, 64)

    #data = uc.mem_read(p_context, 128)
    #print(hexdump(data, p_context))

    print('calling MD5Final(digest, &context)')
    p_digest = x64_alloc_stack(uc, 16)
    print(f'digest allocated to [0x{buf:X}, 0x{buf+16:X})')
    uc.reg_write(UC_X86_REG_RDI, p_digest) # RDI = arg0
    uc.reg_write(UC_X86_REG_RSI, p_context) # RSI = arg1
    x64_push_qword(uc, 0) # return address

    print(f'p_context: 0x{p_context:X}')
    print(f'p_digest: 0x{p_digest:X}')

    uc.emu_start(name2addr['_MD5Final'], 0)

    print('result: (expect: 9e107d9d372bb6826bd81d3542a419d6)')
    data = uc.mem_read(p_digest, 16)
    print(hexdump(data, p_digest))

    #fp_reads.close()
    #fp_writes.close()
