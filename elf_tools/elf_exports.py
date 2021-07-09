#!/usr/bin/env python

# based off http://www.m4b.io/elf/export/binary/analysis/2015/05/25/what-is-an-elf-export.html
#
# (execution view)
# elf header point to list of program headers
#   program headers has an entry for type PT_DYNAMIC (-> SHT_DYNSYM ".dynamic" section)
#     dynamic entries have an antry for DT_SYMTAB (-> SHT_DYNSYM ".dynsym" section)
#     dynamic entries have an entry for DT_STRTAB (-> SHT_STRTAB ".dynstr" section)
#
# (file view)
# elf header points to list of section headers
#   section headers has an entry for type SHT_DYNSYM (usually named ".dynsym")
#     its .sh_link is reference for entry of type SHT_STRTAB (usually named ".dynstr")

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
# elf32_phdr, elf64_phdr
#------------------------------------------------------------------------------
def data_to_elf32_phdr(data):
    (a,b,c,d,e,f,g,h) = struct.unpack('IIIIIIII', data[0:32])
    return { 'p_type':a, 'p_offset':b, 'p_vaddr':c, 'p_paddr':d,
            'p_filesz':e, 'p_memsz':f, 'p_flags':g, 'p_align':h }

def data_to_elf64_phdr(data):
    # WARNING: completely different ordering of fields than elf32_phdr
    (a,b,c,d,e,f,g,h) = struct.unpack('IIQQQQQQ', data[0:56])
    return { 'p_type':a, 'p_flags':b, 'p_offset':c, 'p_vaddr':d,
            'p_paddr':e, 'p_filesz':f, 'p_memsz':g, 'p_align':h }

def data_to_elf_phdr(data, width):
    if width==32: return data_to_elf32_phdr(data)
    else: return data_to_elf64_phdr(data)

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
    struct_size = 40 if width==32 else -1
    (a,b,c,d,e,f,g,h,i,j) = struct.unpack('IIIIIIIIII', data[0:0x28])
    return { 'sh_name':a, 'sh_type':b, 'sh_flags':c, 'sh_addr':d,
            'sh_offset':e, 'sh_size':f, 'sh_link':g, 'sh_info':h,
            'sh_addralign':i, 'sh_entsize':j }

def data_to_elf64_shdr(data):
    struct_size = 40 if width==32 else -1
    (a,b,c,d,e,f,g,h,i,j) = struct.unpack('IIQQQQIIQQ', data[0:0x40])
    return { 'sh_name':a, 'sh_type':b, 'sh_flags':c, 'sh_addr':d,
            'sh_offset':e, 'sh_size':f, 'sh_link':g, 'sh_info':h,
            'sh_addralign':i, 'sh_entsize':j }

def data_to_elf_shdr(data, width):
    if width==32: return data_to_elf32_shdr(data)
    else: return data_to_elf64_shdr(data)

#------------------------------------------------------------------------------
# elf32_sym, elf64_sym
#------------------------------------------------------------------------------

def ELF_ST_BIND(x):
    return x >> 4

def ELF_ST_TYPE(x):
    return x & 0xf

def data_to_elf32_sym(data):
    (a,b,c,d,e,f) = struct.unpack('<IIIBBH', data)
    return {'st_name':a, 'st_value':b, 'st_size':c, 'st_info':d, 'st_other':e, 'st_shndx':f,
      'st_bind':ELF_ST_BIND(d), 'st_type':ELF_ST_TYPE(d)}

def data_to_elf64_sym(data):
    # WARNING: completely different ordering of fields than elf32_sym
    (a,b,c,d,e,f) = struct.unpack('<IBBHQQ', data)
    return {'st_name':a, 'st_info':b, 'st_other':c, 'st_shndx':d, 'st_value':e, 'st_size':f,
      'st_bind':ELF_ST_BIND(b), 'st_type':ELF_ST_TYPE(b)}

def data_to_elf_sym(data, width):
    if width==32: return data_to_elf32_sym(data)
    else: return data_to_elf64_sym(data)

#------------------------------------------------------------------------------
# misc
#------------------------------------------------------------------------------

def chunks(data, width):
    return [data[i:i+width] for i in range(0, len(data), width)]

#------------------------------------------------------------------------------
# main
#------------------------------------------------------------------------------

if __name__ == '__main__':
    data = open(sys.argv[1], 'rb').read()

    width = validate_elf(data)
    if width == 32:
        SIZE_ELF_HDR = 0x34
        SIZE_ELF_PHDR = 0x20
        SIZE_ELF_SHDR = 0x28
        SIZE_ELF_SYM = 0x10
        SIZE_ELF_DYN = 0x8
    else:
        SIZE_ELF_HDR = 0x40
        SIZE_ELF_PHDR = 0x38
        SIZE_ELF_SHDR = 0x40
        SIZE_ELF_SYM = 0x18
        SIZE_ELF_DYN = 0x10
    STB_GLOBAL = 1
    STB_WEAK = 2
    STT_OBJECT = 1
    STT_FUNC = 2
    STT_IFUNC = 10 # mostly sure
    SHN_UNDEF = 0
    SHT_DYNSYM = 11
    PT_DYNAMIC = 2
    DT_STRTAB = 5
    DT_SYMTAB = 6

    ehdr = data_to_elf_hdr(data[0:SIZE_ELF_HDR], width)
    e_shoff = ehdr['e_shoff']

    #print('section header offset: 0x%X\n' % ehdr['e_shoff'])
    #print('section header count: %d\n' % ehdr['e_shnum'])
    
    # scan program headers for .p_type == PT_DYNAMIC
    phdr_claims_offset_dynamic = None
    phdr_claims_offset_dynsym = None
    phdr_claims_offset_dynstr = None
    for i in range(ehdr['e_phnum']):
        offs = ehdr['e_phoff'] + i*SIZE_ELF_PHDR
        phdr = data_to_elf_phdr(data[offs:offs+SIZE_ELF_SHDR], width)
        if phdr['p_type'] != PT_DYNAMIC:
            continue

        #breakpoint()
        phdr_claims_offset_dynamic = phdr['p_offset']
        dyns = [data_to_elf_dyn(chunk, width) for chunk in \
            chunks(data[phdr_claims_offset_dynamic:phdr_claims_offset_dynamic+phdr['p_filesz']], SIZE_ELF_DYN)]

        #print(dyns)
        phdr_claims_offset_dynsym = [d for d in dyns if d['d_tag']==DT_SYMTAB][0]['val_ptr']
        phdr_claims_offset_dynstr = [d for d in dyns if d['d_tag']==DT_STRTAB][0]['val_ptr']
        break
    else:
        assert False, 'no program header with type PT_DYNAMIC'
    assert phdr_claims_offset_dynamic, 'program header missing PT_DYNAMIC'
    assert phdr_claims_offset_dynsym, 'PT_DYNAMIC missing entry DT_SYMTAB'
    assert phdr_claims_offset_dynstr, 'PT_DYNAMIC missing entry DT_STRTAB'

    # scan section table for dynamic symbol section
    strdata = None
    for i in range(ehdr['e_shnum']):
        offs = e_shoff + i*SIZE_ELF_SHDR
        shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
        if shdr['sh_type'] != SHT_DYNSYM:
            continue

        #print('the %dth section header is SHT_DYNSYM' % i)
        assert shdr['sh_offset'] == phdr_claims_offset_dynsym
        dynsyms = [data_to_elf_sym(ch, width) for ch in \
            chunks(data[shdr['sh_offset']: shdr['sh_offset']+shdr['sh_size']], SIZE_ELF_SYM)]

        assert shdr['sh_link'] < ehdr['e_shnum']
        offs = e_shoff + shdr['sh_link']*SIZE_ELF_SHDR
        shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
        assert shdr['sh_offset'] == phdr_claims_offset_dynstr
        dynstr = data[shdr['sh_offset']: shdr['sh_offset']+shdr['sh_size']]

        break
    else:
        assert False, 'no section header with type SHT_DYNSYM'

    # loop over dynamic symbols
    exported_names = []
    for ds in dynsyms:
        if ds['st_value'] == 0: continue
        if ds['st_shndx'] == SHN_UNDEF: continue
        if not ds['st_bind'] in [STB_GLOBAL, STB_WEAK]: continue
        #if not ds['st_bind'] in [STB_GLOBAL]: continue
        if not ds['st_type'] in [STT_FUNC, STT_OBJECT, STT_IFUNC]: continue

        o_str = ds['st_name']
        name = dynstr[o_str: dynstr.find(0, o_str)].decode('utf-8')
        exported_names.append(name)
        #print(name)
        #print(ds)
        #print('----')

    print('\n'.join(sorted(exported_names)))
