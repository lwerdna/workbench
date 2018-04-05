#!/usr/bin/env python

from capstone import *
from struct import pack, unpack

instrWordMax = 0x00100000

csObj = Cs(CS_ARCH_MIPS, CS_MODE_MIPS32)
for instrWord in xrange(0,instrWordMax+1):
	code = pack('>I', instrWord)
	tupleGen = csObj.disasm_lite(code, 0)

	try:
		(addr, sz, mnem, op_str) = tupleGen.next()
		print '%08X %s %s' % (instrWord, mnem, op_str)
	except Exception as e:
		print '%08X undefined' % instrWord
