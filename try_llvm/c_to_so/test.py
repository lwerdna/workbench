#!/usr/bin/env python

import ctypes
import platform

identifier = platform.system() + '-' + platform.machine()

lookup = {
    'Windows-x86': './foo-win-x86.dll',
    'Windows-x86_64': './foo-win-x64.dll',
    'Darwin-x86_64': './foo-macos-x64.dylib',
    'Linux-x86': './foo-linux-x86.so',
    'Linux-x86_64': './foo-linux-x64.so'
}

fname = lookup[identifier]

sharedlib = ctypes.cdll.LoadLibrary(fname)

collatz_next = sharedlib.collatz_next
collatz_next.argtypes = [ctypes.c_int]
collatz_next.restype = ctypes.c_int

print('collatz_next(5) = %d' % collatz_next(5))
print('collatz_next(6) = %d' % collatz_next(6))
print('collatz_next(7) = %d' % collatz_next(7))
print('collatz_next(8) = %d' % collatz_next(8))
