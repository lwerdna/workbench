#!/usr/bin/env python

import re
import sys

from pygdbmi.gdbcontroller import GdbController

def parse_stdout(resp):
    result = ''
    for entry in resp:
        if entry.get('type') == 'console' and entry.get('stream') == 'stdout':
            result += entry.get('payload', '')
    return result

def get_entrypoint(gdbmi):
    resp = gdbmi.write('info file')
    for line in parse_stdout(resp).split('\n'):
        if m := re.search('Entry point: (0x[0-9a-fA-F]+)', line):
            return int(m.group(1), 16)

def get_symbol_address(gdbmi, symname):
    resp = gdbmi.write(f'info address {symname}')
    for line in parse_stdout(resp).split('\n'):
        if m := re.search('is at (0x[0-9a-fA-F]+)', line):
            return int(m.group(1), 16)

def write_mem(gdbmi, address, data):
    if len(data) > 1:
        cmd = 'set {unsigned char[' + str(len(data)) + ']}'
        cmd += hex(address) + ' = "'
        cmd += ''.join(f'\\x{b:02x}' for b in data[0:-1])
        cmd += '"'
        print(f'cmd: {cmd}')
        gdbmi.write(cmd)

    cmd = f'set *(char *){hex(address+len(data)-1)} = {hex(data[-1])}'
    print(f'cmd: {cmd}')
    gdbmi.write(cmd)

def build_loader_stub(addr_dlopen, injected_name):
    stub = b''

    # mov rsi, 2 ; RTLD_NOW
    stub += b'\x48\xc7\xc6\x02\x00\x00\x00'
    # lea rax, rip + ???
    stub += b'\x48\x8d\x05'
    stub += b'\x90\x90\x90\x90'
    # mov rdi, rax
    stub += b'\x48\x89\xc7'
    # mov rax, <address of dlopen>
    stub += b'\x48\xB8'
    stub += addr_dlopen.to_bytes(8, 'little')
    # call rax
    stub += b'\xff\xd0'
    # breakpoint
    stub += b'\xcc'
    # fixup the reference to the string
    offs = 10
    stub = stub[0:offs] + (len(stub)-offs-4).to_bytes(4, 'little') + stub[offs+4:]
    # add string
    stub += injected_name.encode('ascii')

    return stub

if __name__ == '__main__':
    pid = int(sys.argv[1])
    print(f'attaching to pid {pid}')

    gdbmi = GdbController()
    gdbmi.write(f'attach {pid}')
    gdbmi.write('info file')

    entrypoint = get_entrypoint(gdbmi)
    print(f'entrypoint: 0x{entrypoint:x}')

    dlopen = get_symbol_address(gdbmi, 'dlopen')
    print(f'dlopen: 0x{dlopen:x}')

    stub = build_loader_stub(dlopen, 'injected.so')
    #with open('stub.bin', 'wb') as fp:
    #    fp.write(stub)

    write_mem(gdbmi, entrypoint, stub)
