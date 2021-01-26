#!/usr/bin/env python

# compile the .so here
# gcc -shared arm64dis.c -o arm64dis.so

import struct
from ctypes import *

disasmBuff = create_string_buffer(1024)
instBuff =   create_string_buffer(1024)
binja = CDLL("./arm64dis.so")

def disassemble_binja(insword):
    for a in range(len(disasmBuff)):
        disasmBuff[a] = b'\0'
    for a in range(len(instBuff)):
        instBuff[a] = b'\0'
    err = binja.aarch64_decompose(insword, instBuff, 0)
    if err: return None
    if binja.aarch64_disassemble(instBuff, disasmBuff, 128) == 0:
        return disasmBuff.value
    return None

successes = 0
failures = 0
test_i = 0
with open('./test_cases.txt') as fp:
	for line in fp.readlines():
		if line.startswith('//'): continue
		(insword, text) = line.split(' ', 1)

		insword = int(insword, 16)
		instxt = disassemble_binja(insword)

		if instxt:
			#print('%08X: %s' % (insword, disassemble_binja(insword)))
			print(test_i, 1)
			successes += 1
		else:
			#print('None')
			print(test_i, 0)
			failures += 1

		test_i += 1

	print('successes: %d' % successes)
	print('failures: %d' % failures)

