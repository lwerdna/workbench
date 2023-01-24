#!/usr/bin/env python

import sys

import elf64creator

if __name__ == '__main__':
    [fpath_code, fpath_data, imagebase, fpath_output] = sys.argv[1:]

    with open(fpath_code, 'rb') as fp:
        code = fp.read()

    with open(fpath_data, 'rb') as fp:
        data = fp.read()

    print(f'.text: 0x{len(code):X} bytes from {fpath_code}')
    print(f'.data: 0x{len(data):X} bytes from {fpath_data}')

    elf_data = elf64creator.create(code, data, int(imagebase, 16))
    with open(fpath_output, 'wb') as fp:
        print(f'writing 0x{len(elf_data):X} bytes to {fpath_output}')
        fp.write(elf_data)

    print('done')
