import io
import struct

from helpers import *

# code: contents of the text section
# code_addr: virtual address of where the text section should land
def create(code, data, code_addr):
    elf32_hdr_sz = 0x34
    elf32_phdr_sz = 0x20
    elf32_shdr_sz = 0x28

    # SECTION .shstrtab CONTENTS
    shstrtab = b'\x00.text\x00.data\x00.shstrtab\x00'

    # PLAN THE LAYOUT, CALCULATE LOCATIONS
    o = 0

    # ---- ELF header ----
    # <- R-X segment starts here
    o_hdr = o
    o_seg_code_start = o
    o += elf32_hdr_sz
    # ---- program headers (segments of memory)
    o_phdr0 = o
    o += elf32_phdr_sz
    o_phdr1 = o
    o += elf32_phdr_sz
    o_phdr2 = o
    o += elf32_phdr_sz    
    n_program_headers = 3
    o = align_up_to(o, 16)
    # ---- section contents ----
    # .text
    o_text = o
    o += len(code)
    o = align_up_to(o, 16)
    # <- R-X segment ends here
    o_seg_code_end = o
    n_seg_code = o_seg_code_end - o_seg_code_start
    # <- RW- segment starts here
    o_seg_data_start = o
    # .data
    o_data = o
    o += len(data)
    o = align_up_to(o, 16)
    # <- RW- segment ends here
    o_seg_data_end = o
    n_seg_data = o_seg_data_end - o_seg_data_start
    # .shstrtab
    o_shstrtab = o
    o += len(shstrtab)
    o = align_up_to(o, 16)
    # null section header (index: 0)
    i_shdr_null = 0
    o_shdr_null = o
    o += elf32_shdr_sz
    # text section header (index: 1)
    i_shdr_text = 1
    o_shdr_text = o
    o += elf32_shdr_sz
    # data section header (index: 2)
    i_shdr_data = 2
    o_shdr_data = o
    o += elf32_shdr_sz
    file_sz = o    
    # shstrtab section header (index: 3)
    i_shdr_shstrtab = 3
    o_shdr_shstrtab = o
    o += elf32_shdr_sz
    n_section_headers = 4
    file_sz = o

    if code_addr:
        imagebase = code_addr - o_text
    else:
        imagebase = 0x400000
        code_addr = imagebase + o_text

    elf_data = io.BytesIO(b'\x00'*file_sz)

    fields = {  'e_ident': b'\x7FELF',
                'e_ident[EI_CLASS]': 1, # 32 bit
                'e_ident[EI_DATA]': 1, # little vs big end
                'e_ident[EI_VERSION]': 1,
                'e_ident[EI_OSABI]': 0,
                'e_ident[EI_ABIVERSION]': 0,
                'e_ident[EI_PAD]': b'\x00\x00\x00\x00\x00\x00\x00',
                'e_type': 2, # ET_EXEC
                'e_machine': 3, # EM_386
                'e_version': 1,
                'e_entry': code_addr,
                'e_phoff': 0 + elf32_hdr_sz,
                'e_shoff': o_shdr_null,
                'e_flags': 0,
                'e_ehsize': elf32_hdr_sz, # elf header size
                'e_phentsize': elf32_phdr_sz, # program header size
                'e_phnum': n_program_headers,
                'e_shentsize': elf32_shdr_sz, # section header entry size
                'e_shnum': n_section_headers,
                'e_shstrndx': i_shdr_shstrtab # index of shdr that has the string table
    }

    elf32_hdr = struct.pack('<4sBBBBB7sHHIIIIIHHHHHH', *fields.values())
    assert len(elf32_hdr) == elf32_hdr_sz
    elf_data.seek(o_hdr)
    elf_data.write(elf32_hdr)

    # PROGRAM HEADER TABLE

    # FIRST PROGRAM HEADER DESCRIBES THE TABLE ITSELF
    fields = {  'p_type': 6, # PT_PHDR
                'p_offset': 0 + elf32_hdr_sz, # location of program header
                'p_vaddr': imagebase + elf32_hdr_sz, # virtual address of program headers
                'p_paddr': imagebase + elf32_hdr_sz, # physical address program headers
                'p_filesz': n_program_headers * elf32_phdr_sz,
                'p_memsz': n_program_headers * elf32_phdr_sz,
                'p_flags': 5, # R-X
                'p_align': 4
    }

    phdr0 = struct.pack('<IIIIIIII', *fields.values())
    assert len(phdr0) == elf32_phdr_sz
    elf_data.seek(o_phdr0)
    elf_data.write(phdr0)

    # SECOND PROGRAM HEADER LOADS THE EXECUTABLE PORTION OF THIS BINARY TO MEM
    fields = {  'p_type': 1, # PT_LOAD
                'p_offset': 0, # where in this file to start loading
                'p_vaddr': imagebase+o_seg_code_start, # virtual address of program headers
                'p_paddr': imagebase+o_seg_code_start, # physical address program headers
                'p_filesz': n_seg_code,
                'p_memsz': n_seg_code,
                'p_flags': 5, # R-X
                'p_align': 4
    }

    phdr1 = struct.pack('<IIIIIIII', *fields.values())
    assert len(phdr1) == elf32_phdr_sz
    elf_data.seek(o_phdr1)
    elf_data.write(phdr1)

    # THIRD PROGRAM HEADER LOADS THE DATA PORTION OF BINARY TO MEM
    fields = {  'p_type': 1, # PT_LOAD
                'p_offset': o_data, # where in this file to start loading
                'p_vaddr': imagebase+o_seg_data_start, # virtual address of program headers
                'p_paddr': imagebase+o_seg_data_start, # physical address program headers
                'p_filesz': n_seg_data,
                'p_memsz': n_seg_data,
                'p_flags': 6, # RW-
                'p_align': 4
    }

    phdr2 = struct.pack('<IIIIIIII', *fields.values())
    assert len(phdr2) == elf32_phdr_sz
    elf_data.seek(o_phdr2)
    elf_data.write(phdr2)

    # WRITE TEXT SECTION
    elf_data.seek(o_text)
    elf_data.write(code)

    # WRITE DATA SECTION
    elf_data.seek(o_data)
    elf_data.write(data)

    # WRITE SHSTRTAB SECTION
    elf_data.seek(o_shstrtab)
    elf_data.write(shstrtab)

    # FIRST (index 0) SECTION HEADER IS NULL HEADER
    fields = {  'sh_name': 0,
                'sh_type': 0,
                'sh_flags': 0,
                'sh_addr':0,
                'sh_offset': 0,
                'sh_size': 0,
                'sh_link': 0,
                'sh_info': 0,
                'sh_addralign': 0,
                'sh_entsize': 0
    }

    elf32_shdr0 = struct.pack('<IIIIIIIIII', *fields.values())
    assert len(elf32_shdr0) == elf32_shdr_sz
    elf_data.seek(o_shdr_null)
    elf_data.write(elf32_shdr0)

    # SECOND (index 1) SECTION HEADER IS FOR .text
    fields = {  'sh_name': shstrtab.index(b'.text\x00'),
                'sh_type': 1, # PROGBITS (memory initialized with bytes from this file)
                'sh_flags': 6, # SHR_ALLOC|SHF_EXECINSTR
                'sh_addr': imagebase + o_text,
                'sh_offset': o_text,
                'sh_size': len(code),
                'sh_link': 0,
                'sh_info': 0,
                'sh_addralign': 0x10,
                'sh_entsize': 0
    }

    elf32_shdr1 = struct.pack('<IIIIIIIIII', *fields.values())
    assert len(elf32_shdr1) == elf32_shdr_sz
    elf_data.seek(o_shdr_text)
    elf_data.write(elf32_shdr1)

    # THIRD (index 2) SECTION HEADER IS FOR .data
    fields = {  'sh_name': shstrtab.index(b'.data\x00'),
                'sh_type': 1, # PROGBITS (memory initialized with bytes from this file)
                'sh_flags': 3, # SHF_ALLOC|SHF_WRITE
                'sh_addr': imagebase + o_data,
                'sh_offset': o_data,
                'sh_size': len(data),
                'sh_link': 0,
                'sh_info': 0,
                'sh_addralign': 1,
                'sh_entsize': 0
    }

    elf32_shdr2 = struct.pack('<IIIIIIIIII', *fields.values())
    assert len(elf32_shdr2) == elf32_shdr_sz
    elf_data.seek(o_shdr_data)
    elf_data.write(elf32_shdr2)

    # FOURTH (index 3) SECTION HEADER IS FOR .shstrtab
    fields = {  'sh_name': shstrtab.index(b'.shstrtab\x00'),
                'sh_type': 3, # STRTAB
                'sh_flags': 0,
                'sh_addr': 0, # doesn't get mapped
                'sh_offset': o_shstrtab,
                'sh_size': len(shstrtab),
                'sh_link': 0,
                'sh_info': 0,
                'sh_addralign': 1,
                'sh_entsize': 0
    }

    elf32_shdr3 = struct.pack('<IIIIIIIIII', *fields.values())
    assert len(elf32_shdr3) == elf32_shdr_sz
    elf_data.seek(o_shdr_shstrtab)
    elf_data.write(elf32_shdr3)

    # RETURN
    elf_data.seek(0)
    return elf_data.read()
