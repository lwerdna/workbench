#!/usr/bin/env python

import os, sys, re, pprint

JTAG = False

print('flags0 = SegmentFlag.SegmentExecutable | SegmentFlag.SegmentContainsCode | SegmentFlag.SegmentReadable')
print('flags1 = SegmentFlag.SegmentContainsData | SegmentFlag.SegmentReadable')

fname = 'blob_jtag.bin' if JTAG else 'blob.bin'

with open('blob.bin', 'wb') as fp:
    # [0, 32k)
    start = fp.tell()
    data = open('internalMem_first32KB.bin', 'rb').read()
    fp.write(data)
    end = fp.tell()
    assert end == 32768
    print(f'bv.add_user_segment(0, 0x8000, 0x{start:X}, 0x{end-start:X}, flags0)')

    if JTAG:
        # [0x40000000, 0x40300000]
        start = fp.tell()
        data = open('externalMem_first3MB.bin', 'rb').read()
        fp.write(data)
        end = fp.tell()
        assert end == 32768 + 3145728
        print(f'bv.add_user_segment(0x40000000, 0x40300000, 0x{start:X}, 0x{end-start:X}, flags0)')
    else:
        # [0x40000000, 0x43000000]
        start = fp.tell()
        data = open('externalMem_first8MB.bin', 'rb').read()
        fp.write(data)
        end = fp.tell()
        length = end - start
        assert length == 8388608
        assert end == 32768 + length

        print(f'bv.add_user_segment(0x40000000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')
        print(f'bv.add_user_segment(0x40800000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')
        print(f'bv.add_user_segment(0x41000000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')
        print(f'bv.add_user_segment(0x41800000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')
        print(f'bv.add_user_segment(0x42000000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')
        print(f'bv.add_user_segment(0x42800000, 0x{length:X}, 0x{start:X}, 0x{end-start:X}, flags0)')

    start = fp.tell()
    data = open('48000000.bin', 'rb').read()
    fp.write(data)
    end = fp.tell()
    if JTAG:
        assert end == 32768 + 3145728 + 1048576
    else:
        assert end == 32768 + 8388608 + 1048576
    print(f'bv.add_user_segment(0x48000000, 0x480100000, 0x{start:X}, 0x{end-start:X}, flags1)')
