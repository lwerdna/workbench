#!/usr/bin/env python

import os
import sys
import re
import readline

from ctypes import *

if __name__ == '__main__':
    dll = CDLL('./gofer.so')
    assert dll
    
    # void *gofer_initialize()
    dll.gofer_initialize.restype = c_void_p
    result = dll.gofer_initialize()
    print(f'returned: 0x{result:X}')

    # void *gofer_malloc(size_t size)
    dll.gofer_malloc.restype = c_void_p
    dll.gofer_malloc.argtypes = [c_size_t]

    # void gofer_free(void *p)
    dll.gofer_free.restype = None
    dll.gofer_free.argtypes = [c_void_p]

    while 1:
        inp = input('SHELL> ')

        if inp == 'quit':
            break

        elif m := re.match(r'^malloc (.*)$', inp):
            amount = m.group(1)
            amount = int(amount, 10 if amount.isdigit() else 16)
            result = dll.gofer_malloc(amount)
            print(f'gofer_malloc() returned: 0x{result:X}')

        elif m := re.match(r'^free (.*)$', inp):
            addr = m.group(1)
            addr = int(addr, 16)
            dll.gofer_free(addr)

        elif m := re.match(r'^fill', inp):
            amount = 1
            while True:
                result = dll.gofer_malloc(amount)
                if result == None:
                    print(f'filled')
                    break
                print(f'gofer_malloc(0x{amount:X} returned: 0x{result:X}')
                amount *= 2


