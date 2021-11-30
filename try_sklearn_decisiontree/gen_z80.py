#!/usr/bin/env python

import os
import sys
import struct

#------------------------------------------------------------------------------
# skoolkit/disassembler
#------------------------------------------------------------------------------

from skoolkit import disassembler

# skoolkit wants a 64k "snapshot" of memory, in the form of a bytes or list object
# we provide a fake snapshot that can position a few bytes to any area within the 64k mem
class CustomSnapshot():
	def __init__(self, data, addr):
		self.data = data
		self.base = addr

	def check_idx(self, idx):
		if idx < self.base or (idx - self.base) > len(self.data):
			raise IndexError

	def __getitem__(self, key):
		#print('__getitem__(%s)' % repr(key))

		if type(key) == int:
			self.check_idx(key)
			result = self.data[key-self.base]
		elif type(key) == slice:
			self.check_idx(key.start)
			self.check_idx(key.stop)
			result = self.data[key.start-self.base : key.stop-self.base]
		else:
			raise TypeError
			
		return result

disObj = None

def disasm(data, addr):
	#print('addr: %d, data: %s' % (addr, str(data)))
	global disObj

	if not disObj:
		disObj = disassembler.Disassembler(data, asm_hex=True)
	
	disObj.snapshot = CustomSnapshot(data, addr)

	decoder, template = disObj.ops[data[0]]

	try:
		if template is None:
			instrTxt, instrLen = decoder(disObj, addr, None)
		else:
			instrTxt, instrLen = decoder(disObj, template, addr, None)
	except IndexError:
		instrTxt, instrLen = '<error>', 0

	if instrTxt.startswith('DEFB'):
		instrTxt, instrLen = '<error>', 0

	return(instrTxt, instrLen)

#------------------------------------------------------------------------------
# main
#------------------------------------------------------------------------------

opc2id = { 'ADC': 1, 'ADD': 2, 'AND': 3, 'BIT': 4, 'CALL': 5, 'CCF': 6, 'CP':
7, 'CPD': 8, 'CPDR': 9, 'CPI': 10, 'CPIR': 11, 'CPL': 12, 'DAA': 13, 'DEC': 14,
'DI': 15, 'DJNZ': 16, 'EI': 17, 'EX': 18, 'EXX': 19, 'HALT': 20, 'IM': 21,
'IN': 22, 'INC': 23, 'IND': 24, 'INDR': 25, 'INI': 26, 'INIR': 27, 'JP': 28,
'JR': 29, 'LD': 30, 'LDD': 31, 'LDDR': 32, 'LDI': 33, 'LDIR': 34, 'NEG': 35,
'NOP': 36, 'OR': 37, 'OTDR': 38, 'OTIR': 39, 'OUT': 40, 'OUTD': 41, 'OUTI': 42,
'POP': 43, 'PUSH': 44, 'RES': 45, 'RET': 46, 'RETI': 47, 'RETN': 48, 'RL': 49,
'RLA': 50, 'RLC': 51, 'RLCA': 52, 'RLD': 53, 'RR': 54, 'RRA': 55, 'RRC': 56,
'RRCA': 57, 'RRD': 58, 'RST': 59, 'SBC': 60, 'SCF': 61, 'SET': 62, 'SLA': 63,
'SLL': 64, 'SRA': 65, 'SRL': 66, 'SUB': 67, 'XOR': 68, 'UNDEF':69 }

# 0xFF00 -> '[1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,F,F,0,0,FF,00]'
def uint16_to_varstr(insword):
	bits = map(lambda x: str(int(bool(insword & (1<<x)))), range(15,-1,-1))
	nybbles = map(lambda x: str(int(  (insword & (0xF<<x))>>x  )), [12, 8, 4, 0])
	bytes_ = map(hex, [insword>>8, insword&0xff])
	return '['+','.join(bits)+','+','.join(nybbles)+','+','.join(bytes_)+']'


if __name__ == '__main__':
	if 0:
		opcs = set()
		for insword in range(65536):
			data = struct.pack('>H', insword) + b'\x00\x00'
			(distxt, dislen) = disasm(data, 0)
			print('%02X %02X: %s' % (insword>>8, insword&0xFF, distxt))
			opcs.add(distxt.split(' ')[0])

		print('all opcodes: ')
		for i,opc in enumerate(sorted(opcs)):
			print('%s: %d' % (opc,i))
		sys.exit(-1)

	allopcs = set()

	print('input_names = [', end='')
	for i in range(15,-1,-1):
		print('\'b%d\',' % i, end='')
	print("'nybble3', 'nybble2', 'nybble1', 'nybble0', ", end='')
	print("'byte1', 'byte0'", end='')
	print(']')

	output_data = []
	print('input_data = [')
	for insword in range(65536):
		data = struct.pack('>H', insword)

		(distxt,dislen) = disasm(data+b'\x00\x00', 0)
		if 'error' in distxt:
			opc = 'UNDEF'
		else:
			opc = distxt.split(' ')[0]

		allopcs.add(opc)
		output_data.append(opc2id[opc])

		print('\t' + uint16_to_varstr(insword) + ',')
	print(']')

	print('output_names = [', end='')
	for (i,opc) in enumerate(sorted(allopcs)):
		print('\'%s\',' % (opc), end='')
	print(']')

	print('output_data = [', end='')
	print(','.join(map(str, output_data)), end='')
	print(']')

