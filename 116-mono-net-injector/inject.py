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
    assembly_path = sys.argv[1]
    pid = int(sys.argv[2])

    # change with:
    # echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope
    fpath = '/proc/sys/kernel/yama/ptrace_scope'
    if os.path.exists(fpath):
        with open(fpath) as fp:
            if fp.read().startswith('1'):
                print(f'WARNING: ptrace may be limited by {fpath}')
                print(f'   HINT: echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope')

    # check path to assembly
    if not os.path.isabs(assembly_path):
        assembly_path = os.path.abspath(assembly_path)
    if not os.path.exists(assembly_path):
        print(f'ERROR: {assembly_path} does not exist')
        sys.exit(-1)

    # check path to stage1
    stage1_path = os.path.join(os.getcwd(), 'stage1.so')
    if not os.path.exists(stage1_path):
        print(f'ERROR: {stage1_path} does not exist')
        sys.exit(-1)

    gdbmi = GdbController()
    gdb(gdbmi, f'attach {pid}')

    # get stage1 to memory
    lines = gdb(gdbmi, f'call dlopen("{stage1_path}", 2)')
    handle = int(re.search(r' 0x([a-fA-F0-9]+)', lines[-1]).group(1), 16)
    print(f'shared object loaded to: 0x{handle:X}')

    # call stage1 with path to stage2 (the .net dll)
    gdb(gdbmi, f'call (void)load_assembly_call_method("{assembly_path}", "FooNamespace", "FooClass", "FooMethod")')

    # cleanup
    gdb(gdbmi, f'call dlclose(0x{handle:X})')
    gdb(gdbmi, f'detach')
