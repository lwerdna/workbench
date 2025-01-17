#!/usr/bin/env python

import re
import os
import sys

from pygdbmi.gdbcontroller import GdbController

# execute a gdb command, return output lines
def gdb(gdbmi, command):
    print(f'(gdb) {command}')
    response = gdbmi.write(command)
    #print(response)
    return [x['payload'] for x in response if x['type']=='console']

if __name__ == '__main__':
    sopath = sys.argv[1]
    pid = int(sys.argv[2])

    # change with:
    # echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope
    fpath = '/proc/sys/kernel/yama/ptrace_scope'
    if os.path.exists(fpath):
        with open(fpath) as fp:
            if fp.read().startswith('1'):
                print(f'WARNING: ptrace may be limited by {fpath}')
                print(f'   HINT: echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope')

    if not os.path.isabs(sopath):
        sopath = os.path.abspath(sopath)

    print(f'injecting {sopath} into pid {pid}')

    gdbmi = GdbController()
    gdb(gdbmi, f'attach {pid}')

    lines = gdb(gdbmi, f'call dlopen("{sopath}", 2)')
    breakpoint()
    handle = int(re.search(r' 0x([a-fA-F0-9]+)', lines[-1]).group(1), 16)
    print(f'shared object loaded to: 0x{handle:X}')

    gdb(gdbmi, f'call (void)load_assembly_call_method("/path/to/foo.dll", "FooNamespace", "FooClass", "FooMethod")')
    gdb(gdbmi, f'call dlclose(0x{handle:X})')
    gdb(gdbmi, f'detach')
