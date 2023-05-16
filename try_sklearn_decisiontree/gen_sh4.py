#!/usr/bin/env python

import os
import sys
import struct

# pip install sh4dis
from sh4dis import sh4

opc2id = {
'add': 0, 'addc': 1, 'addv': 2, 'and': 3, 'and.b': 4, 'bf': 5, 'bf.s': 6,
'bra': 7, 'braf': 8, 'bsr': 9, 'bsrf': 10, 'bt': 11, 'bt.s': 12, 'clrmac': 13,
'clrs': 14, 'clrt': 15, 'cmp/eq': 16, 'cmp/ge': 17, 'cmp/gt': 18, 'cmp/hi': 19,
'cmp/hs': 20, 'cmp/pl': 21, 'cmp/pz': 22, 'cmp/str': 23, 'div0s': 24, 'div0u':
25, 'div1': 26, 'dmuls.l': 27, 'dmulu.l': 28, 'dt': 29, 'exts.b': 30, 'exts.w':
31, 'extu.b': 32, 'extu.w': 33, 'fabs': 34, 'fadd': 35, 'fcmp/eq': 36,
'fcmp/gt': 37, 'fcnvds': 38, 'fcnvsd': 39, 'fdiv': 40, 'fipr': 41, 'fldi0': 42,
'fldi1': 43, 'flds': 44, 'float': 45, 'fmac': 46, 'fmov': 47, 'fmul': 48,
'fneg': 49, 'frchg': 50, 'fsca': 51, 'fschg': 52, 'fsqrt': 53, 'fsrra': 54,
'fsts': 55, 'fsub': 56, 'ftrc': 57, 'ftrv': 58, 'jmp': 59, 'jsr': 60, 'ldc':
61, 'ldc.l': 62, 'lds': 63, 'lds.l': 64, 'ldtlb': 65, 'mac.l': 66, 'mac.w': 67,
'mov': 68, 'mov.b': 69, 'mov.l': 70, 'mov.w': 71, 'mova': 72, 'movca.l': 73,
'movt': 74, 'mul.l': 75, 'muls.w': 76, 'mulu.w': 77, 'neg': 78, 'negc': 79,
'nop': 80, 'not': 81, 'ocbi': 82, 'ocbp': 83, 'ocbwb': 84, 'or': 85, 'or.b':
86, 'pref': 87, 'rotcl': 88, 'rotcr': 89, 'rotl': 90, 'rotr': 91, 'rte': 92,
'rts': 93, 'sets': 94, 'sett': 95, 'shad': 96, 'shal': 97, 'shar': 98, 'shld':
99, 'shll': 100, 'shll16': 101, 'shll2': 102, 'shll8': 103, 'shlr': 104,
'shlr16': 105, 'shlr2': 106, 'shlr8': 107, 'sleep': 108, 'stc': 109, 'stc.l':
110, 'sts': 111, 'sts.l': 112, 'sub': 113, 'subc': 114, 'subv': 115, 'swap.b':
116, 'swap.w': 117, 'tas.b': 118, 'trapa': 119, 'tst': 120, 'tst.b': 121,
'undef': 122, 'xor': 123, 'xor.b': 124, 'xtrct': 125, 'error': 126
}

def input_bit_vars(insword):
	bits = map(lambda x: str(int(bool(insword & (1<<x)))), range(15,-1,-1))
	return '['+','.join(bits)+']'

def input_bits_nybbles_vars(insword):
	bits = map(lambda x: str(int(bool(insword & (1<<x)))), range(15,-1,-1))
	nybbles = map(lambda x: str(int(  (insword & (0xF<<x))>>x  )), [12, 8, 4, 0])
	return '['+','.join(bits)+','+','.join(nybbles)+']'

if __name__ == '__main__':
	allopcs = set()

	print('input_names = [', end='')
	for i in range(15,-1,-1):
		print('\'b%d\',' % i, end='')
	print("'nybble3', 'nybble2', 'nybble1', 'nybble0'", end='')
	print(']')

	output_data = []
	print('input_data = [')
	for insword in range(65536):
		data = struct.pack('>H', insword)

		b = sh4.disasm(insword, 0)
		if not b or b.startswith('.word'):
			opc = 'undef'
		else:
			opc = b.split(' ')[0]

		allopcs.add(opc)

		if not opc in opc2id:
		    breakpoint()
		output_data.append(opc2id[opc])

		inp_repr_func = input_bits_nybbles_vars
		#print('%04X: %s: %s' % (insword, inp_repr_func(insword), opc))
		print('\t' + inp_repr_func(insword) + ',')
	print(']')

	print('output_names = [', end='')
	for (i,opc) in enumerate(sorted(allopcs)):
		print('\'%s\',' % (opc), end='')
	print(']')

	print('output_data = [', end='')
	print(','.join(map(str, output_data)), end='')
	print(']')

