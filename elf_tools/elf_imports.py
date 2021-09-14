#!/usr/bin/env python

# get list of imported libraries

import os, sys, struct

#------------------------------------------------------------------------------
# elf32_hdr, elf64_hdr
#------------------------------------------------------------------------------

def validate_elf(data):
    assert data[0:4] == b"\x7fELF" # e_ident[0..4)
    if data[4] == 1: width = 32 # ELFCLASS32
    elif data[4] == 2: width = 64 # ELFCLASS64
    else: assert False
    assert data[6] == 1 # e_ident[EI_VERSION] should be version 1
    return width

def data_to_elf32_hdr(data):
    (a,b,c,d,e,f,g,h,i,j,k,l,m) = \
        struct.unpack('HHIIIIIHHHHHH', data[16:16+0x34-16])
    return { 'e_type':a, 'e_machine':b, 'e_version':c, 'e_entry':d, 'e_phoff':e,
            'e_shoff':f, 'e_flags':g, 'e_ehsize':h, 'e_phentsize':i,
            'e_phnum':j, 'e_shentsize':k, 'e_shnum':l, 'e_shstrndx':m }

def data_to_elf64_hdr(data):
    (a,b,c,d,e,f,g,h,i,j,k,l,m) = \
        struct.unpack('HHIQQQIHHHHHH', data[16:16+0x40-16])
    return { 'e_type':a, 'e_machine':b, 'e_version':c, 'e_entry':d, 'e_phoff':e,
            'e_shoff':f, 'e_flags':g, 'e_ehsize':h, 'e_phentsize':i,
            'e_phnum':j, 'e_shentsize':k, 'e_shnum':l, 'e_shstrndx':m }

def data_to_elf_hdr(data, width):
    if width==32: return data_to_elf32_hdr(data)
    else: return data_to_elf64_hdr(data)

#------------------------------------------------------------------------------
# elf32_dyn, elf64_dyn
#------------------------------------------------------------------------------
def data_to_elf32_dyn(data):
    (a,b) = struct.unpack('II', data[0:8])
    return { 'd_tag':a, 'val_ptr':b }

def data_to_elf64_dyn(data):
    (a,b) = struct.unpack('QQ', data[0:16])
    return { 'd_tag':a, 'val_ptr':b }

def data_to_elf_dyn(data, width):
    if width==32: return data_to_elf32_dyn(data)
    else: return data_to_elf64_dyn(data)

#------------------------------------------------------------------------------
# elf32_shdr, elf64_shdr
#------------------------------------------------------------------------------
def data_to_elf32_shdr(data):
    (a,b,c,d,e,f,g,h,i,j) = struct.unpack('IIIIIIIIII', data[0:0x28])
    return { 'sh_name':a, 'sh_type':b, 'sh_flags':c, 'sh_addr':d,
            'sh_offset':e, 'sh_size':f, 'sh_link':g, 'sh_info':h,
            'sh_addralign':i, 'sh_entsize':j }

def data_to_elf64_shdr(data):
    (a,b,c,d,e,f,g,h,i,j) = struct.unpack('IIQQQQIIQQ', data[0:0x40])
    return { 'sh_name':a, 'sh_type':b, 'sh_flags':c, 'sh_addr':d,
            'sh_offset':e, 'sh_size':f, 'sh_link':g, 'sh_info':h,
            'sh_addralign':i, 'sh_entsize':j }

def data_to_elf_shdr(data, width):
    if width==32: return data_to_elf32_shdr(data)
    else: return data_to_elf64_shdr(data)

#------------------------------------------------------------------------------
# main
#------------------------------------------------------------------------------

def get_imports(fpath):
    results = []

    data = open(fpath, 'rb').read()

    width = validate_elf(data)
    if width == 32:
        SIZE_ELF_HDR = 0x34
        SIZE_ELF_SHDR = 0x28
        SIZE_ELF_DYN = 0x8
    else:
        SIZE_ELF_HDR = 0x40
        SIZE_ELF_SHDR = 0x40
        SIZE_ELF_DYN = 0x10
    SHT_STRTAB = 3
    SHT_DYNSYM = 11
    SHT_DYNAMIC = 6
    DT_NEEDED = 1

    ehdr = data_to_elf_hdr(data[0:SIZE_ELF_HDR], width)

    # get pointer to section headers
    e_shoff = ehdr['e_shoff']

    # read section header string table
    offs = e_shoff + ehdr['e_shstrndx']*SIZE_ELF_SHDR
    shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
    strtab = data[shdr['sh_offset']:shdr['sh_offset']+shdr['sh_size']]

    def get_strtab_entry(i, table):
        tmp = table[i:]
        tmp = tmp[0:tmp.find(b'\x00')]
        return tmp.decode('utf-8')

    # scan section table for dynamic symbol section
    shdr_dynamic = None
    shdr_dynsym = None
    shdr_dynstr = None
    for i in range(ehdr['e_shnum']):
        offs = e_shoff + i*SIZE_ELF_SHDR
        shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
        if get_strtab_entry(shdr['sh_name'], strtab)=='.dynamic' and shdr['sh_type'] == SHT_DYNAMIC:
            shdr_dynamic = shdr
        if get_strtab_entry(shdr['sh_name'], strtab)=='.dynsym' and shdr['sh_type'] == SHT_DYNSYM:
            shdr_dynsym = shdr
        if get_strtab_entry(shdr['sh_name'], strtab)=='.dynstr' and shdr['sh_type'] == SHT_STRTAB:
            shdr_dynstr = shdr
    if not (shdr_dynamic and shdr_dynsym and shdr_dynstr):
        print('.dynamic, .dynsym, or .dynstr missing, assuming no imports')
        return []

    strtab = data[shdr_dynstr['sh_offset']:shdr_dynstr['sh_offset']+shdr_dynstr['sh_size']]

    # loop over .dynamic section for entry with DT_NEEDED
    tmp = data[shdr_dynamic['sh_offset']:shdr_dynamic['sh_offset']+shdr_dynamic['sh_size']]
    while tmp:
        dyn_entry = data_to_elf_dyn(tmp, width)
        if dyn_entry['d_tag'] == DT_NEEDED:
            dll = get_strtab_entry(dyn_entry['val_ptr'], strtab)
            results.append(dll)
        tmp = tmp[SIZE_ELF_DYN:]

    return results

if __name__ == '__main__':
    fpath = sys.argv[1]
    imports = get_imports(fpath)
    print(imports)

