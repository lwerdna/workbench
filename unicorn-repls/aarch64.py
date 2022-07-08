#!/usr/bin/env python
# an assembly REPL for aarch64 execution environment (A64 instruction set)

# pip install keystone-engine
# pip install unicorn

import re
import struct
import readline

from unicorn import *
from unicorn.arm64_const import *

from keystone import *

from termcolor import colored

from helpers import *

rname_to_unicorn = {
	'x0': UC_ARM64_REG_X0, 'x1': UC_ARM64_REG_X1, 'x2': UC_ARM64_REG_X2, 'x3': UC_ARM64_REG_X3,
	'x4': UC_ARM64_REG_X4, 'x5': UC_ARM64_REG_X5, 'x6': UC_ARM64_REG_X6, 'x7': UC_ARM64_REG_X7,
	'x8': UC_ARM64_REG_X8, 'x9': UC_ARM64_REG_X9, 'x10': UC_ARM64_REG_X10, 'x11': UC_ARM64_REG_X11,
	'x12': UC_ARM64_REG_X12, 'x13': UC_ARM64_REG_X13, 'x14': UC_ARM64_REG_X14, 'x15': UC_ARM64_REG_X15,
	'x16': UC_ARM64_REG_X16, 'x17': UC_ARM64_REG_X17, 'x18': UC_ARM64_REG_X18, 'x19': UC_ARM64_REG_X19,
	'x20': UC_ARM64_REG_X20, 'x21': UC_ARM64_REG_X21, 'x22': UC_ARM64_REG_X22, 'x23': UC_ARM64_REG_X23,
	'x24': UC_ARM64_REG_X24, 'x25': UC_ARM64_REG_X25, 'x26': UC_ARM64_REG_X26, 'x27': UC_ARM64_REG_X27,
	'x28': UC_ARM64_REG_X28, 'x29': UC_ARM64_REG_X29, 'x30': UC_ARM64_REG_X30,
	'fp': UC_ARM64_REG_FP, # or UC_ARM64_REG_X29
	'lr': UC_ARM64_REG_LR, # or UC_ARM64_REG_X30
	'nzcv': UC_ARM64_REG_NZCV,
	'pc': UC_ARM64_REG_PC,
	'sp': UC_ARM64_REG_SP,
}

# set up emulator, assembler
ADDRESS = 0x1000000
ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)	
mu = Uc(UC_ARCH_ARM64, UC_MODE_LITTLE_ENDIAN)
mu.mem_map(0, 4096)
mu.mem_map(ADDRESS, 4096)

# track context

regs_old = [-1]*33
def show_context():
	global mu
	global regs_old

	reg_ids = [
		UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3,
		UC_ARM64_REG_X4, UC_ARM64_REG_X5, UC_ARM64_REG_X6, UC_ARM64_REG_X7,
		UC_ARM64_REG_X8, UC_ARM64_REG_X9, UC_ARM64_REG_X10, UC_ARM64_REG_X11,
		UC_ARM64_REG_X12, UC_ARM64_REG_X13, UC_ARM64_REG_X14, UC_ARM64_REG_X15,
		UC_ARM64_REG_X16, UC_ARM64_REG_X17, UC_ARM64_REG_X18, UC_ARM64_REG_X19,
		UC_ARM64_REG_X20, UC_ARM64_REG_X21, UC_ARM64_REG_X22, UC_ARM64_REG_X23,
		UC_ARM64_REG_X24, UC_ARM64_REG_X25, UC_ARM64_REG_X26, UC_ARM64_REG_X27,
		UC_ARM64_REG_X28, UC_ARM64_REG_FP, UC_ARM64_REG_LR, UC_ARM64_REG_PC,
		UC_ARM64_REG_NZCV
	]

	regs = [mu.reg_read(x) for x in reg_ids]
	regs_str = ['%016X' % x for x in regs]
	regs_str = [x if regs[i]==regs_old[i] else colored(x, 'red') for (i,x) in enumerate(regs_str)]

	# special handling of nzcv
	(n,z,c,v) = (bool(regs[32] & 0x80000000), bool(regs[32] & 0x40000000), \
		bool(regs[32] & 0x20000000), bool(regs[32] & 0x10000000))

	# show context
	print(' x0=%s  x1=%s  x2=%s  x3=%s' % (regs_str[0], regs_str[1], regs_str[2], regs_str[3]))
	print(' x4=%s  x5=%s  x6=%s  x7=%s' % (regs_str[4], regs_str[5], regs_str[6], regs_str[7]))
	print(' x8=%s  x9=%s x10=%s x11=%s' % (regs_str[8], regs_str[9], regs_str[10], regs_str[11]))
	print('x12=%s x13=%s x14=%s x15=%s' % (regs_str[12], regs_str[13], regs_str[14], regs_str[15]))
	print('x16=%s x17=%s x18=%s x19=%s' % (regs_str[16], regs_str[17], regs_str[18], regs_str[19]))
	print('x20=%s x21=%s x22=%s x23=%s' % (regs_str[20], regs_str[21], regs_str[22], regs_str[23]))
	print('x24=%s x25=%s x26=%s x27=%s' % (regs_str[24], regs_str[25], regs_str[26], regs_str[27]))
	print('x28=%s  fp=%s  lr=%s' % (regs_str[28], regs_str[29], regs_str[30]))
	print(' pc=%s  nzcv=%s (N=%d Z=%d C=%d V=%d)' % (regs_str[31], regs_str[32], n, z, c, v))

	regs_old = regs

while 1:
	cmd = input('> ')

	isasm = True

	try:
		m = re.match(r'.regset (.*) (.*)', cmd)
		if m:
			(rname, rval) = m.group(1, 2)
			mu.reg_write(rname_to_unicorn[rname], int(rval, 16))
			isasm = False

		m = re.match(r'.db (.*)', cmd)
		if m:
			addr = int(m.group(1),16)
			data = mu.mem_read(addr, 64)
			print(get_hex_dump(data, addr))
			isasm = False

		m = re.match(r'.raw (.*)', cmd)
		if m:
			arg = m.group(1)
			data = b''.join([int(x, 16).to_bytes(1,'big') for x in arg.split()])
			print('writing:', colored(data.hex(), 'green'))
			mu.mem_write(ADDRESS, data)
			isasm = False
			mu.emu_start(ADDRESS, ADDRESS + len(data))

		if isasm and cmd:
			encoding, count = ks.asm(cmd)
			data = b''.join([x.to_bytes(1,'big') for x in encoding])
			print('assembles to:', colored(data.hex(), 'green'))
			mu.mem_write(ADDRESS, data)
			mu.emu_start(ADDRESS, ADDRESS + len(encoding))

	except KsError as e:
		print('keystone error:', e)

	except UcError as e:
		print(e)
		print(type(e))
		print(dir(e))
		print(e.args)
		print('unicorn error:', e)

	show_context()
