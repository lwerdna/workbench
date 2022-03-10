#!/usr/bin/env python

# an assembly REPL for x86

import re
import readline

from unicorn import *
from unicorn.x86_const import *

from keystone import *

rname_to_unicorn = {
	'eax': UC_X86_REG_EAX, 'ebx': UC_X86_REG_EBX, 'ecx': UC_X86_REG_ECX, 'edx': UC_X86_REG_EDX,
	'esp': UC_X86_REG_ESP, 'ebp': UC_X86_REG_EBP, 'esi': UC_X86_REG_ESI, 'edi': UC_X86_REG_EDI,
	'eip': UC_X86_REG_EIP, 'eflags': UC_X86_REG_EFLAGS,
	'cs': UC_X86_REG_CS, 'ss': UC_X86_REG_SS, 'ds': UC_X86_REG_DS, 'es': UC_X86_REG_ES,
	'fs': UC_X86_REG_FS, 'gs': UC_X86_REG_GS
}

# set up emulator, assembler
ADDRESS = 0x1000000
ks = Ks(KS_ARCH_X86, KS_MODE_32)	
mu = Uc(UC_ARCH_X86, UC_MODE_32)
mu.mem_map(ADDRESS, 4096)

while 1:
	cmd = input('> ')

	isasm = True

	try:
		m = re.match(r'.regset (.*) (.*)', cmd)
		if m:
			(rname, rval) = m.group(1, 2)
			mu.reg_write(rname_to_unicorn[rname], int(rval, 16))
			isasm = False
	
		if isasm:
			encoding, count = ks.asm(cmd)
			data = b''.join([x.to_bytes(1,'big') for x in encoding])
			#print('encoding: %s (%d bytes)' % (str(data), len(data)))
			mu.mem_write(ADDRESS, data)
			mu.emu_start(ADDRESS, ADDRESS + len(encoding))

	except KsError as e:
		print('keystone error:', e)

	except UcError as e:
		print('unicorn error:', e)

	# show context
	print('eax=%08X ebx=%08X ecx=%08X edx=%08X' % \
		(mu.reg_read(UC_X86_REG_EAX), mu.reg_read(UC_X86_REG_EBX), \
		mu.reg_read(UC_X86_REG_ECX), mu.reg_read(UC_X86_REG_EDX)))
	print('esp=%08X ebp=%08X esi=%08X edi=%08X' % \
		(mu.reg_read(UC_X86_REG_ESP), mu.reg_read(UC_X86_REG_EBP), 
		mu.reg_read(UC_X86_REG_ESI), mu.reg_read(UC_X86_REG_EDI)))
	print(' cs=%08X  ss=%08X' % \
		(mu.reg_read(UC_X86_REG_CS), mu.reg_read(UC_X86_REG_SS)))
	print(' ds=%08X  es=%08X' % \
		(mu.reg_read(UC_X86_REG_DS), mu.reg_read(UC_X86_REG_ES)))
	print(' fs=%08X  gs=%08X' % \
		(mu.reg_read(UC_X86_REG_FS), mu.reg_read(UC_X86_REG_GS)))
	print('eip=%08X eflags=%08X' % \
		(mu.reg_read(UC_X86_REG_EIP), mu.reg_read(UC_X86_REG_EFLAGS)))
