#!/usr/bin/env python

import os
import sys
import re
import random
import readline

from PIL import Image

from ctypes import *

# must match CORE_MEM_SZ in gofer
CORE_MEM_SZ = 1024*1024

palette = [
    0x00007F, 0x000084, 0x000088, 0x00008D, 0x000091, 0x000096, 0x00009A,
    0x00009F, 0x0000A3, 0x0000A8, 0x0000AC, 0x0000B1, 0x0000B6, 0x0000BA,
    0x0000BF, 0x0000C3, 0x0000C8, 0x0000CC, 0x0000D1, 0x0000D5, 0x0000DA,
    0x0000DE, 0x0000E3, 0x0000E8, 0x0000EC, 0x0000F1, 0x0000F5, 0x0000FA,
    0x0000FE, 0x0000FF, 0x0000FF, 0x0000FF, 0x0000FF, 0x0004FF, 0x0008FF,
    0x000CFF, 0x0010FF, 0x0014FF, 0x0018FF, 0x001CFF, 0x0020FF, 0x0024FF,
    0x0028FF, 0x002CFF, 0x0030FF, 0x0034FF, 0x0038FF, 0x003CFF, 0x0040FF,
    0x0044FF, 0x0048FF, 0x004CFF, 0x0050FF, 0x0054FF, 0x0058FF, 0x005CFF,
    0x0060FF, 0x0064FF, 0x0068FF, 0x006CFF, 0x0070FF, 0x0074FF, 0x0078FF,
    0x007CFF, 0x0080FF, 0x0084FF, 0x0088FF, 0x008CFF, 0x0090FF, 0x0094FF,
    0x0098FF, 0x009CFF, 0x00A0FF, 0x00A4FF, 0x00A8FF, 0x00ACFF, 0x00B0FF,
    0x00B4FF, 0x00B8FF, 0x00BCFF, 0x00C0FF, 0x00C4FF, 0x00C8FF, 0x00CCFF,
    0x00D0FF, 0x00D4FF, 0x00D8FF, 0x00DCFE, 0x00E0FA, 0x00E4F7, 0x02E8F4,
    0x05ECF1, 0x08F0ED, 0x0CF4EA, 0x0FF8E7, 0x12FCE4, 0x15FFE1, 0x18FFDD,
    0x1CFFDA, 0x1FFFD7, 0x22FFD4, 0x25FFD0, 0x29FFCD, 0x2CFFCA, 0x2FFFC7,
    0x32FFC3, 0x36FFC0, 0x39FFBD, 0x3CFFBA, 0x3FFFB7, 0x42FFB3, 0x46FFB0,
    0x49FFAD, 0x4CFFAA, 0x4FFFA6, 0x53FFA3, 0x56FFA0, 0x59FF9D, 0x5CFF9A,
    0x5FFF96, 0x63FF93, 0x66FF90, 0x69FF8D, 0x6CFF89, 0x70FF86, 0x73FF83,
    0x76FF80, 0x79FF7D, 0x7CFF79, 0x80FF76, 0x83FF73, 0x86FF70, 0x89FF6C,
    0x8DFF69, 0x90FF66, 0x93FF63, 0x96FF5F, 0x9AFF5C, 0x9DFF59, 0xA0FF56,
    0xA3FF53, 0xA6FF4F, 0xAAFF4C, 0xADFF49, 0xB0FF46, 0xB3FF42, 0xB7FF3F,
    0xBAFF3C, 0xBDFF39, 0xC0FF36, 0xC3FF32, 0xC7FF2F, 0xCAFF2C, 0xCDFF29,
    0xD0FF25, 0xD4FF22, 0xD7FF1F, 0xDAFF1C, 0xDDFF18, 0xE0FF15, 0xE4FF12,
    0xE7FF0F, 0xEAFF0C, 0xEDFF08, 0xF1FC05, 0xF4F802, 0xF7F400, 0xFAF000,
    0xFEED00, 0xFFE900, 0xFFE500, 0xFFE200, 0xFFDE00, 0xFFDA00, 0xFFD700,
    0xFFD300, 0xFFCF00, 0xFFCB00, 0xFFC800, 0xFFC400, 0xFFC000, 0xFFBD00,
    0xFFB900, 0xFFB500, 0xFFB100, 0xFFAE00, 0xFFAA00, 0xFFA600, 0xFFA300,
    0xFF9F00, 0xFF9B00, 0xFF9800, 0xFF9400, 0xFF9000, 0xFF8C00, 0xFF8900,
    0xFF8500, 0xFF8100, 0xFF7E00, 0xFF7A00, 0xFF7600, 0xFF7300, 0xFF6F00,
    0xFF6B00, 0xFF6700, 0xFF6400, 0xFF6000, 0xFF5C00, 0xFF5900, 0xFF5500,
    0xFF5100, 0xFF4D00, 0xFF4A00, 0xFF4600, 0xFF4200, 0xFF3F00, 0xFF3B00,
    0xFF3700, 0xFF3400, 0xFF3000, 0xFF2C00, 0xFF2800, 0xFF2500, 0xFF2100,
    0xFF1D00, 0xFF1A00, 0xFF1600, 0xFE1200, 0xFA0F00, 0xF50B00, 0xF10700,
    0xEC0300, 0xE80000, 0xE30000, 0xDE0000, 0xDA0000, 0xD50000, 0xD10000,
    0xCC0000, 0xC80000, 0xC30000, 0xBF0000, 0xBA0000, 0xB60000, 0xB10000,
    0xAC0000, 0xA80000, 0xA30000, 0x9F0000, 0x9A0000, 0x960000, 0x910000,
    0x8D0000, 0x880000, 0x840000, 0x7F0000
]

def rgb_hex_to_tuple(h):
    return (h>>16, (h>>8)&0xFF, h&0xFF)

def malloc(dll, amount):
    addr = dll.gofer_malloc(amount)

    if addr == None:
        print(f'gofer_malloc() returned: 0 (it failed)')
    else:
        print(f'gofer_malloc() returned: 0x{addr:X}')

        # mark allocated bytes with 0x80
        dll.gofer_memset(addr, 0x80, amount);

    return addr

def free(dll, addr, size=None):
    # mark free'd bytes with 0xF0
    if size:
        dll.gofer_memset(addr, 0xF0, size);

    dll.gofer_free(addr)

if __name__ == '__main__':
    dll = CDLL('./gofer.so')
    assert dll
    
    # void *gofer_initialize()
    dll.gofer_initialize.restype = c_void_p
    result = dll.gofer_initialize()
    print(f'returned: 0x{result:X}')

    # void *gofer_malloc(size_t size)
    dll.gofer_malloc.restype = c_void_p
    dll.gofer_malloc.argtypes = [c_size_t]

    # void gofer_free(void *p)
    dll.gofer_free.restype = None
    dll.gofer_free.argtypes = [c_void_p]

    # void gofer_get_core(unsigned char *p)
    dll.gofer_get_core.restype = None
    dll.gofer_get_core.argtypes = [c_void_p]

    # void *gofer_memset(void *buf, unsigned char c, size_t n)
    dll.gofer_memset.restype = c_void_p
    dll.gofer_memset.argtypes = [c_void_p, c_char, c_size_t]

    buf_to_sz = {}

    while 1:
        inp = input('SHELL> ')

        if inp == 'quit':
            break

        elif m := re.match(r'^malloc (.*)$', inp):
            size = m.group(1)
            size = int(size, 10 if size.isdigit() else 16)
            addr = malloc(dll, size)
            buf_to_sz[addr] = size

        elif m := re.match(r'^free (.*)$', inp):
            addr = m.group(1)
            addr = int(addr, 16)
            free(dll, addr, buf_to_sz[addr])
            del buff_to_sz[addr]

        elif m := re.match(r'^fill', inp):
            size = 1
            while True:
                result = malloc(dll, size)
                if result == None:
                    print(f'filled')
                    break
                size *= 2

        elif inp in ['pic', 'picture']:
            p = create_string_buffer(1024*1024)
            dll.gofer_get_core(byref(p))
            with open('core.bin', 'wb') as fp:
                fp.write(p.raw)
            img = Image.new('RGB', (1024, 1024))
            img_data = [rgb_hex_to_tuple(palette[x]) for x in p.raw]
            img.putdata(img_data)
            img.save("/tmp/tmp.png")

        elif inp == 'fun':
            p = create_string_buffer(1024*1024)

            for i in range(200):
                action = 'malloc' if not buf_to_sz else random.choice(['malloc', 'free'])
                match action:
                    # allocate a random buffer
                    case 'malloc':
                        size = random.randint(1*1024, 128*1024)
                        addr = malloc(dll, size)
                        buf_to_sz[addr] = size
                    # free a random buffer
                    case 'free':
                        addr = random.choice(list(buf_to_sz.keys()))
                        if addr == 0:
                            breakpoint()
                        size = buf_to_sz[addr]
                        free(dll, addr, size)
                        del buf_to_sz[addr]

                dll.gofer_get_core(byref(p))
                img = Image.new('RGB', (1024, 1024))
                img_data = [rgb_hex_to_tuple(palette[x]) for x in p.raw]
                img.putdata(img_data)
                fpath = f'./frames/frame{i:08d}.png'
                print(f'writing {fpath}')
                img.save(fpath)
