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
    print(__file__)

    if len(sys.argv) < 5 + 1:
        print(f'usage:')
        print(f'  {sys.argv[0]} <pid> <dll> <namespace> <class> <method>')
        print(f'usage:')
        print(f'  {sys.argv[0]} 1234 test.dll MyNamespace MyClass MyMethod')
        sys.exit(0)

    path_stage1 = os.path.join(os.path.split(__file__)[0], 'stage1.so')

    pid = int(sys.argv[1])
    path_assembly = sys.argv[2]
    inj_namespace = sys.argv[3]
    inj_class = sys.argv[4]
    inj_method = sys.argv[5]

    # change with:
    # echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope
    fpath = '/proc/sys/kernel/yama/ptrace_scope'
    if os.path.exists(fpath):
        with open(fpath) as fp:
            if fp.read().startswith('1'):
                print(f'WARNING: ptrace may be limited by {fpath}')
                print(f'   HINT: echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope')

    # check path to assembly
    if not os.path.isabs(path_assembly):
        path_assembly = os.path.abspath(path_assembly)
    if not os.path.exists(path_assembly):
        print(f'ERROR: {path_assembly} does not exist')
        sys.exit(-1)

    # check path to stage1
    if not os.path.exists(path_stage1):
        print(f'ERROR: {stage1_path} does not exist')
        sys.exit(-1)

    gdbmi = GdbController()
    gdb(gdbmi, f'attach {pid}')

    # get stage1 to memory
    lines = gdb(gdbmi, f'call dlopen("{path_stage1}", 2)')
    handle = int(re.search(r' 0x([a-fA-F0-9]+)', lines[-1]).group(1), 16)
    print(f'shared object loaded to: 0x{handle:X}')

    # call stage1 with path to stage2 (the .net dll)
    gdb(gdbmi, f'call (void)load_assembly_call_method("{path_assembly}", "{inj_namespace}", "{inj_class}", "{inj_method}")')

    # cleanup
    gdb(gdbmi, f'call dlclose(0x{handle:X})')
    gdb(gdbmi, f'detach')
