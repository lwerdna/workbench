#!/usr/bin/env python

import re
import struct
from skoolkit_testing import skoolkit_disasm

conds = ['C', 'NC', 'Z', 'NZ', 'M', 'P', 'PE', 'PO']
regs8 = list('ABDHCELIR') + ['A\'', 'B\'', 'C\'', 'D\'', 'E\'', 'H\'', 'L\'', 'Flags', 'Flags\'', 'IXh', 'IXl', 'IYh', 'IYl']
regs16 = ['AF', 'BC', 'DE', 'HL', 'AF', 'AF\'', 'BC\'', 'DE\'', 'HL\'', 'IX', 'IY', 'SP', 'PC']
regs = regs8 + regs16

opcs = ['ADC', 'ADD', 'AND', 'BIT', 'CALL', 'CCF', 'CP', 'CPD', 'CPDR',
		'CPI', 'CPIR', 'CPL', 'DAA', 'DEC', 'DI', 'DJNZ', 'EI', 'EX',
		'EXX', 'HALT', 'IM', 'IN', 'INC', 'IND', 'INDR', 'INI', 'INIR',
		'IN_F', 'JP', 'JR', 'LD', 'LDD', 'LDDR', 'LDI', 'LDIR', 'LD_A_I',
		'LD_A_R', 'LD_R_A', 'NEG', 'NOP', 'NOP*', 'OR', 'OTDR', 'OTIR',
		'OUT', 'OUTD', 'OUTI', 'POP', 'PUSH', 'RES', 'RET', 'RETI',
		'RETN', 'RL', 'RLA', 'RLC', 'RLCA', 'RLD', 'RR', 'RRA', 'RRC',
		'RRCA', 'RRD', 'RST', 'SBC', 'SCF', 'SET', 'SLA', 'SLL', 'SRA',
		'SRL', 'SUB', 'XOR',
		
		'DEFB']

# PROBLEM: cond 'C' conflicts with register C
# eg: "RET C" is it "RET <reg>" or "REG <cc>" ?
# eg: "CALL C" is it "CALL <reg>" or "CALL <cc>" ?
def z80_syntax(instrTxt):
	tokens = [t for t in re.split(r'([, ()\+])', instrTxt) if t]
	#print 'tokens: ', tokens

	types = []
	for tok in tokens:
		if not tok or tok == ' ': continue
		elif tok == 'C' and tokens[0] in ['CALL','RET']: types.append('CC')
		elif tok in regs16: types.append('REG16')
		elif tok in regs8: types.append('REG8')
		elif tok in conds: types.append('CC')
		elif tok[0] == '#': types.append('IMM')
		elif tok.startswith('$'): types.append('VAL16')
		elif tok.isdigit(): types.append('VAL10')
		elif tok in opcs: types.append('OPC')
		elif tok in [',', '(', ')', '+']: types.append(tok)
		else: raise Exception('unfamiliar token: %s from instruction %s' % (tok, instrTxt))

	syntax = tokens[0]
	if types[1:]:
		syntax = tokens[0] + ' ' + ' '.join(types[1:])

	return syntax

syns = set()
for k in range(65536):
	data = list(struct.pack('>I', k << 16))
	instrTxt, instrLen = skoolkit_disasm(0, data)
	if instrLen:
		instrSyn = z80_syntax(instrTxt)
		print('%02X %02X 00 00: %s %s' % (data[0], data[1], instrTxt, instrSyn))
		syns.add(instrSyn)

print('\n'.join(sorted(syns)))
