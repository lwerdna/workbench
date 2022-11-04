#!/usr/bin/env python

import sys
import time
import random

from capstone import *
from struct import pack

quiet = sys.argv[1:] and sys.argv[1]=='quiet'

t0 = time.time()
NUM_TESTS = 1000000
suite = [pack('<I', random.randint(0, 0xFFFFFFFF)) for i in range(NUM_TESTS)]
if not quiet:
    print("suite generation: %fs" % (time.time()-t0))

t0 = time.time()
cs_obj = Cs(CS_ARCH_ARM, CS_MODE_ARM)
if not quiet:
    print("setup time: %fs" % (time.time()-t0))

t0 = time.time()
for code in suite:
    tuple_gen = cs_obj.disasm_lite(code, 0)

    try:
        (addr, sz, mnem, op_str) = next(tuple_gen)
        if not quiet:
            print('%s: %s %s' % (code.hex(), mnem, op_str))
    except Exception as e:
        if not quiet:
            print('%s: undefined' % code.hex())

delta = time.time()-t0
print("total time: %fs for %d tests (%f instrs/sec)" % \
    (delta, NUM_TESTS, NUM_TESTS/delta))
