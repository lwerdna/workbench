#!/usr/bin/env python

import re
import os
import sys
from struct import pack, unpack

#------------------------------------------------------------------------------
# ELF STUFF
#------------------------------------------------------------------------------

def readScnHdr(fp, strtab, bits, endian):
    """ read section header, annotate with 'nameStr' if strtab provided """
    assert bits in [32, 64]
    assert endian in ['little', 'big']

    oHdr = fp.tell()

    keys = ['name', 'type', 'flags', 'addr', 'offset', 'size', 'link', \
        'info', 'addralign', 'entsize']

    if bits == 32:
        # elf32_shdr
        shdr_len = 0x28
        fmtstr = '<IIIIIIIIII' if endian == 'little' else '>IIIIIIIIII'
    if bits == 64:
        # elf64_shdr
        shdr_len = 0x40
        fmtstr = '<IIQQQQIIQQ' if endian == 'little' else '>IIQQQQIIQQ'
    values = list(unpack(fmtstr, fp.read(shdr_len)))

    # additional field 'nameStr': name of section (resolve name offset)
    if strtab:
        keys.append('nameStr')
        offset = values[0]
        values.append(strtab[offset:offset+strtab[offset:].find(b'\x00')])

    # additional field 'oHdr': offset within file that this section is found
    keys.append('oHdr')
    values.append(oHdr)

    return dict(zip(keys, values))

def getTextSection(fp):
    """ retrieve the section header """

    fp.seek(0)
    assert fp.read(4) == ELFMAG
    elf_class = unpack('B', fp.read(1))[0] # e_ident[EI_CLASS]
    assert elf_class in [ELFCLASS32, ELFCLASS64]
    bits = 32 if elf_class == ELFCLASS32 else 64
    ei_data = unpack('B', fp.read(1))[0] # e_ident[EI_DATA]
    assert ei_data in [ELFDATA2LSB, ELFDATA2MSB]
    endian = 'little' if ei_data == ELFDATA2LSB else 'big'

    fp.seek(16)

    if bits == 32:
        # elf32_hdr
        ehdr_len = 0x24
        shdr_len = 0x28
        fmtstr = '<HHIIIIIHHHHHH' if endian == 'little' else '>HHIIIIIHHHHHH'
    if bits == 64:
        # elf64_hdr
        ehdr_len = 0x30
        shdr_len = 0x40
        fmtstr = '<HHIQQQIHHHHHH' if endian == 'little' else '>HHIQQQIHHHHHH'
    (_, _, _, _, _, e_shoff, _, _, _, _, _, e_shnum, e_shstrndx) = \
        unpack(fmtstr, fp.read(ehdr_len))

    # get strtab
    fp.seek(e_shoff + e_shstrndx * shdr_len)
    tmp = readScnHdr(fp, None, bits, endian)
    fp.seek(tmp['offset'])
    stringTable = fp.read(tmp['size'])

    # loop over sections until .text is found
    for i in range(e_shnum):
        fp.seek(e_shoff + i * shdr_len)
        tmp = readScnHdr(fp, stringTable, bits, endian)
        #print('trying: %s' % tmp['nameStr'])
        if tmp['nameStr'] == b'.text': 
            fp.seek(tmp['offset'])
            return fp.read(tmp['size'])

ELFMAG = b'\x7FELF'

ELFLCASSNONE = 0
ELFCLASS32 = 1
ELFCLASS64 = 2

ELFDATANONE = 0
ELFDATA2LSB = 1
ELFDATA2MSB = 2

EV_NONE = 0
EV_CURRENT = 1

def isElf(fp):
    elf_class = None
    tmp = fp.tell()
    fp.seek(0)
    if fp.read(4) != ELFMAG:
        #print('MISSING ELFMAG')
        return False
    elf_class = unpack('B', fp.read(1))[0] # e_ident[EI_CLASS]
    if not (elf_class in [ELFCLASS32, ELFCLASS64]):
        #print('MISSING elf_class32 or elf_class64')
        return False
    ei_data = unpack('B', fp.read(1))[0] # e_ident[EI_DATA]
    if not ei_data in [ELFDATA2LSB, ELFDATA2MSB]:
        #print('MISSING ELFDATA2LSB or ELFDATA2MSB')
        return False
    ei_version = unpack('B', fp.read(1))[0]
    if not ei_version in [EV_CURRENT]: # e_ident[EI_VERSION]
        #print('WRONG ei_version')
        return False
    fp.seek(tmp)
    return (True, elf_class, ei_data)

def isElf64(fp):
    """ test if fp points to an elf64 file """
    result = isElf(fp)
    return result and result[1] == ELFCLASS64

def isElf32(fp):
    """ test if fp points to an elf32 file """
    result = isElf(fp)
    return result and result[1] == ELFCLASS32

#------------------------------------------------------------------------------
# MAIN
#------------------------------------------------------------------------------

def normalize(a):
	s = float(sum(a))
	result = list(map(lambda x: x/s, a))
	assert abs(sum(result) - 1) < .001
	return result

def histogram_from_buffer(buff):
    result = [0]*256
    for byte in buff:
        result[byte] += 1
    return result

def histogram_from_file(fpath):
    fp = open(fpath, 'rb')
    assert isElf32(fp) or isElf64(fp)
    text_section = getTextSection(fp)
    #print(str(text_section[0:8]) + '...' + str(text_section[-8:]))
    if not text_section:
        raise Exception('NO TEXT SECTION')    
    result = histogram_from_buffer(text_section)
    fp.close()
    return result

def histogram_pretty_print(data, name='data'):
    print('%s = [' % name)
    while data:
        chunk = data[0:8]
        data = data[8:]
        print('    ' + ', '.join(map(lambda x: '%2.6f'%x, chunk)), end='')
        print(',' if data else '')
    print(']\n')

if __name__ == '__main__':
    fpath = sys.argv[1]
    data = histogram_from_file(fpath)
    data = normalize(data)
    #print(sum(data))
    name = 'histogram_' + re.sub(r'\W', '_', os.path.split(fpath)[1])
    histogram_pretty_print(data, name)

