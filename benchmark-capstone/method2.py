#!/usr/bin/env python
#
# python method0: ctypes through a binary gofer

import sys
import struct
import random
import ctypes
import time

quiet = sys.argv[1:] and sys.argv[1]=='quiet'

t0 = time.time()
NUM_TESTS = 1000000
suite = [struct.pack('<I', random.randint(0, 0xFFFFFFFF)) for i in range(NUM_TESTS)]
if not quiet:
    print("suite generation: %fs" % (time.time()-t0))

t0 = time.time()
gofer = ctypes.CDLL("gofer.so")
cbuf = ctypes.create_string_buffer(256)
if not quiet:
    print("types: %fs" % (time.time()-t0))

t0 = time.time()
for data in suite:
    gofer.get_disasm_capstone(data, 4, ctypes.byref(cbuf))

    if not quiet:
        print('%s: %s' % (data.hex(), cbuf.value))

delta = time.time()-t0
print("total time: %fs for %d tests (%f instrs/sec)" %
    (delta, NUM_TESTS, NUM_TESTS/delta))


