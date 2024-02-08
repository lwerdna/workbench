#!/usr/bin/env python

import io
import os
import struct

def align_up_to(x, alignment):
    residue = x % alignment
    if residue:
        return x + (alignment - residue)
    return x

if __name__ == '__main__':
    elf32_hdr_sz = 0x34
    elf32_phdr_sz = 0x20
    elf32_shdr_sz = 0x28

    # PLAN THE LAYOUT, CALCULATE LOCATIONS
    o = 0

    # ---- ELF header ----
    # <- R-X segment starts here
    o_hdr = o
    o_seg_code_start = o
    o += elf32_hdr_sz
    # ---- program headers (segments of memory)
    o_program_headers = o
    n_program_headers = 8
    o += n_program_headers * elf32_phdr_sz
    # ---- blob of files
    o = align_up_to(o, 16)
    o_blob0 = o
    o += os.path.getsize('internalMem_first32KB.bin')
    o_blob1 = o
    o += os.path.getsize('externalMem_first8MB.bin')
    o_blob2 = o
    o += os.path.getsize('48000000.bin')
    
    file_sz = o
    imagebase = 0xF0000000
    elf_data = io.BytesIO(b'\x00'*file_sz)
    fields = {  'e_ident': b'\x7FELF',
                'e_ident[EI_CLASS]': 1, # 32 bit
                'e_ident[EI_DATA]': 1, # little-end
                'e_ident[EI_VERSION]': 1,
                'e_ident[EI_OSABI]': 0,
                'e_ident[EI_ABIVERSION]': 0,
                'e_ident[EI_PAD]': b'\x00\x00\x00\x00\x00\x00\x00',
                'e_type': 2, # ET_EXEC
                'e_machine': 0x28, # EM_ARM
                'e_version': 1,
                'e_entry': 0,
                'e_phoff': 0 + elf32_hdr_sz,
                'e_shoff': 0,
                'e_flags': 0x5000000,
                'e_ehsize': elf32_hdr_sz, # elf header size
                'e_phentsize': elf32_phdr_sz, # program header size
                'e_phnum': n_program_headers,
                'e_shentsize': elf32_shdr_sz, # section header entry size
                'e_shnum': 0,
                'e_shstrndx': 0 # index of shdr that has the string table
    }

    elf32_hdr = struct.pack('<4sBBBBB7sHHIIIIIHHHHHH', *fields.values())
    assert len(elf32_hdr) == elf32_hdr_sz
    elf_data.seek(o_hdr)
    elf_data.write(elf32_hdr)

    # PROGRAM HEADER TABLES
    entries = [
        ('internalMem_first32KB.bin', o_blob0, 0),
        ('externalMem_first8MB.bin', o_blob1, 0x40000000),
        ('externalMem_first8MB.bin', o_blob1, 0x40800000),
        ('externalMem_first8MB.bin', o_blob1, 0x41000000),
        ('externalMem_first8MB.bin', o_blob1, 0x41800000),
        ('externalMem_first8MB.bin', o_blob1, 0x42000000),
        ('externalMem_first8MB.bin', o_blob1, 0x42800000),
        ('48000000.bin', o_blob2, 0x48000000)
    ]

    for i, (fname, offset, vaddr) in enumerate(entries):
        size = os.path.getsize(fname)

        fields = {  'p_type': 1, # PT_LOAD
                    'p_offset': offset,
                    'p_vaddr': vaddr,
                    'p_paddr': vaddr,
                    'p_filesz': size,
                    'p_memsz': size,
                    'p_flags': 5, # R-X
                    'p_align': 4
        }
        phdr = struct.pack('<IIIIIIII', *fields.values())
        assert len(phdr) == elf32_phdr_sz
        elf_data.seek(o_program_headers + i*elf32_phdr_sz)
        elf_data.write(phdr)

    # BLOB
    elf_data.seek(o_blob0)
    elf_data.write(open('internalMem_first32KB.bin', 'rb').read())
    elf_data.seek(o_blob1)
    elf_data.write(open('externalMem_first8MB.bin', 'rb').read())
    elf_data.seek(o_blob2)
    elf_data.write(open('48000000.bin', 'rb').read())


    # RETURN
    elf_data.seek(0)
    
    with open('result.elf', 'wb') as fp:
        fp.write(elf_data.read())
