#!/usr/bin/env python

# based off http://www.m4b.io/elf/export/binary/analysis/2015/05/25/what-is-an-elf-export.html
# - in a section type SHT_SYMTAB or SHT_DYNSYM (usually ".dynsym") you have array of:
#
#typedef struct {
#        Elf32_Word      st_name;   // idx to string table
#        Elf32_Addr      st_value;  // address, offset, ??? (it depends)
#        Elf32_Word      st_size;
#        unsigned char   st_info;   // binding, type, info
#        unsigned char   st_other;
#        Elf32_Half      st_shndx;
#} Elf32_Sym;
#
# criteria
#   - .st_value != 0
#   - .st_shndx != 0 (SHN_UNDEF)
#   - .st_info.bind \in {GLOBAL, WEAK}
#   - .st_info.type \in {FUNC, IFUNC, OBJECT}
#
# - in a section type SHT_DYNAMIC (usually ".dynamic") you should find
#   array of Elf32_Dyn or Elf64_Dyn with:
#   ???

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

    ehdr = data_to_elf_hdr(data[0:SIZE_ELF_HDR], width)
    e_shoff = ehdr['e_shoff']

    #print('section header offset: 0x%X\n' % ehdr['e_shoff'])
    #print('section header count: %d\n' % ehdr['e_shnum'])

    # find dynamic symbol section
    strdata = None
    for i in range(ehdr['e_shnum']):
        offs = e_shoff + i*SIZE_ELF_SHDR
        shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
        if shdr['sh_type'] != 11: # SHT_DYNSYM
            continue

        #print('the %dth section header is SHT_DYNSYM' % i)
        dynsyms = [data_to_elf_sym(ch, width) for ch in \
            chunks(data[shdr['sh_offset']: shdr['sh_offset']+shdr['sh_size']], SIZE_ELF_SYM)]

        assert shdr['sh_link'] < ehdr['e_shnum']
        offs = e_shoff + shdr['sh_link']*SIZE_ELF_SHDR
        shdr = data_to_elf_shdr(data[offs:offs+SIZE_ELF_SHDR], width)
        dynstr = data[shdr['sh_offset']: shdr['sh_offset']+shdr['sh_size']]

        break
    else:
        assert False

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
