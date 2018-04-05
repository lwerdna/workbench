#!/usr/bin/env python

import re
import struct
import ctypes

thunk = ctypes.CDLL("binthunk.so")
cbuf = ctypes.create_string_buffer(256)

instrWordMax = 0x00100000

for instrWord in xrange(0,instrWordMax+1):
	data = struct.pack('>I', instrWord)
	rc = thunk.get_disasm_capstone(data, 4, ctypes.byref(cbuf))
	if rc: raise Exception("ERROR: get_disasm_capstone()")
	print '%08X %s' % (instrWord, cbuf.value)

