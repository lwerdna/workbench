#!/usr/bin/env python

import os, sys
import subprocess

import algorithm

blacklist_extensions = ['.rot13', '.dex', '.txt', '.bmp', '.jpg', '.png', '.gif', '.col', '.class', '.bndb', '.gz', '.rom', '.rot32', '.jpeg', '.c', '.zip', '.rar', '.gpg', '.nes']
blacklist_filenames = ['Makefile', 'wtf_arch_29a-unknown-x64.elf', 'elf_29a', 'hello-sh4', 'babymips-nanomips', 'mame']

def get_arch_via_file(fpath):
    output = subprocess.check_output(['file', fpath]).decode('utf-8')
    if '80386' in output or 'DOS executable' in output:
        return 'x86'
    if 'x86-64' in output or 'x86_64' in output:
        return 'x86_64'
    if ', ARM,' in output:
        return 'armv7'
    if ', Renesas SH,' in output:
        return 'Renesas SH'
    if '-nanomips-' in output:
        return 'nanomips'
    if 'PowerPC ' in output or 'executable ppc' in output:
        return 'ppc'
    if 'aarch64' in output or 'arm64e' in output:
        return 'aarch64'
    if 'MIPS64' in output:
        return 'mips64'
    if 'MIPS' in output:
        return 'mips32'
    else:
        print(output)
        breakpoint()

if __name__ == '__main__':
    arg = sys.argv[1]

    queue = []
    if os.path.isfile(arg):
        queue.append(arg)
    elif os.path.isdir(arg):
        for fname in os.listdir(arg):
            if fname in blacklist_filenames:
                continue
            if any([fname.endswith(ext) for ext in blacklist_extensions]):
                continue
            fpath = os.path.join(arg, fname)
            queue.append(fpath)
    else:
        assert False

    print('\n'.join(queue))
    
    print('path'.ljust(64), 'us'.ljust(10), 'file'.ljust(10), 'result')
    for fpath in queue:
        arch_file = get_arch_via_file(fpath)
        arch_us = algorithm.guess_architecture(fpath)

        match = 'MATCH!' if arch_file == arch_us else ''
        print(fpath.ljust(64), arch_us.ljust(10), arch_file.ljust(10), match)
        
