#!/usr/bin/env python

import os
import sys

from helpers import *

from aardvark_py import *

if __name__ == '__main__':
    addr = 0
    length = 256

    if sys.argv[1:]:
        base = 16 if sys.argv[1].startswith('0x') else 10
        addr = int(sys.argv[1], base)
    if sys.argv[2:]:
        base = 16 if sys.argv[1].startswith('0x') else 10
        length = int(sys.argv[2], base)

    # 8-bit addresses only
    addr = addr & 0xFF

    print(f'reading 0x{length:X} bytes from 0x{addr:X}')

    # other flags: AA_I2C_10_BIT_ADDR | AA_I2C_COMBINED_FMT | AA_I2C_NO_STOP | AA_I2C_SIZED_READ | AA_I2C_SIZED_READ_EXTRA1
    flags = AA_I2C_NO_FLAGS

    aardvark_handle = open_aardvark()
    if aardvark_handle < 0:
        print(f"error opening aardvark '{aa_status_string(aardvark_handle)}'")
        sys.exit(1)

    # supported bitrates: 100, 200, 307, 400, 500, 615, 727, 800
    aa_i2c_bitrate(aardvark_handle, 100)

    data = read_eeprom(aardvark_handle, addr, length)

    if not data:
        print('ERROR: no data')
        sys.exit(-1)

    print(hexdump(data))

    # INF-8074i Rev 1.0 May 12, 2001
    # Table 3.4. Transceiver codes
    if addr==0 and length==256:
        data = data.tobytes()
        print(f'Identifier: {data[0]}')
        print(f'Ext. Identifier: {data[1]}')
        print(f'Connector: {data[2]}')
        print(f'BR, Nominal: {data[12]}')
        print(f'Vendor name: {data[20:35+1]}')
        print(f'Vendor OUI: {data[37:39+1]}')
        print(f'Vendor PN: {data[40:55+1]}')
        print(f'Vendor rev: {data[56:59+1]}')
        print(f'Vendor SN: {data[68:83+1]}')
        print(f'Date code: {data[84:91+1]}')
