#!/usr/bin/env python

# DOESNT WORK!
# attempt to brute force query clang for its supported triples

import os, sys, re, pprint
import subprocess

import itertools

def shellout(cmd):
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (stdout, stderr) = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    print('stdout: -%s-' % stdout)
    print('stderr: -%s-' % stderr)
    process.wait()
    return (stdout, stderr)

if __name__ == '__main__':
    stdout, _ = shellout(['clang', '-print-targets'])

    # lines are like:
    # "    arm64_32   - ARM64 (little endian ILP32)"
    # "    x86-64     - 64-bit X86: EM64T and AMD64"
    archs = []
    for line in stdout.split('\n'):
        m = re.match(r'^\s+([^ ]+)\s*- ', line)
        if not m: continue
        archs.append(m.group(1))

    print('architectures:', ','.join(archs))

    subs = ['v5', 'v6m', 'v7a', 'v7m']
    vendors = ['pc', 'apple', 'nvidia', 'ibm']
    syss = ['unknown', 'linux', 'win32', 'win64', 'darwin', 'cuda']
    abis = ['eabi', 'gnu', 'gnueabi-ld', 'android', 'androideabi', 'macho', 'elf']

    for attempt in itertools.product(archs, subs, vendors, syss, abis):
        triplet = '-'.join(attempt)
        rc = subprocess.call(['clang', '-target', triplet, '-c', './foo.c'])
        if rc == 0:
            print(triplet)
