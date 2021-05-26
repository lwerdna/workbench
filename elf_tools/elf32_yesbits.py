#!/usr/bin/env python

import re
import sys
import struct

fpath = sys.argv[1]
fp = open(fpath, 'rb+')
# read elf32_hdr
assert fp.read(4) == b"\x7fELF" # e_ident[0..4)
assert fp.read(1) == b"\x01" # e_ident[EI_CLASS] should be 32-bit
assert fp.read(1) == b"\x01" # e_ident[EI_DATA] should be little-end
assert fp.read(1) == b"\x01" # e_ident[EI_VERSION] should be version 1
fp.read(1+1+7) # EI_OSABI, EI_ABIVERSION, EI_PAD
fp.seek(16) # to elf32_hdr.e_type
(x,x,x,e_entry,e_phoff,e_shoff,x,x,x,e_phnum,x,e_shnum,e_shstrndx) = \
    struct.unpack('HHIIIIIHHHHHH', fp.read(2+2+4+4+4+4+4+2+2+2+2+2+2))

fp.seek(e_phoff)
for i in range(e_phnum):
	mark = fp.tell()
	print('at file offset 0x%X' % mark)

	(p_type,p_flags,p_offset,p_vaddr,p_paddr,p_filesz,p_memsz,p_align) = \
		struct.unpack('IIIIIIII', fp.read(32))
	print('phdr type=%X flags=%X offset=%X vaddr=%X paddr=%X filesz=%X memsz=%X align=%X' % \
		(p_type,p_flags,p_offset,p_vaddr,p_paddr,p_filesz,p_memsz,p_align))

	if p_memsz < p_filesz:
		input('section memsz < filesz, expanding, press any key to continue...')
		p_memsz = p_filesz
		fp.seek(mark)
		fp.write(struct.pack('IIIIIIII', p_type,p_flags,p_offset,p_vaddr,p_paddr,p_filesz,p_memsz,p_align))
	
fp.seek(e_shoff)
for i in range(e_shnum):
	mark = fp.tell()
	print('at file offset 0x%X' % mark)

	(sh_name,sh_type,sh_flags,sh_addr,sh_offset,sh_size,sh_link,sh_info,sh_addralign,sh_entsize) = \
		struct.unpack('IIIIIIIIII', fp.read(40))
	print('shdr sh_name=%X sh_type=%X sh_flags=%X sh_addr=%X sh_offset=%X sh_size=%X sh_link=%X sh_info=%X sh_addralign=%X sh_entsize=%X' % \
		(sh_name,sh_type,sh_flags,sh_addr,sh_offset,sh_size,sh_link,sh_info,sh_addralign,sh_entsize))

	# for ALLOC|EXECINSTR sections, toggle NOBITS
	if sh_flags==6 and sh_type==8:
		input('setting executable NOBITS section to PROGBITS, press any key to continue...')
		sh_type = 1 # PROGBITS
		fp.seek(mark)
		fp.write(struct.pack('IIIIIIIIII', sh_name,sh_type,sh_flags,sh_addr,sh_offset,sh_size,sh_link,sh_info,sh_addralign,sh_entsize))
		
	
		
		


