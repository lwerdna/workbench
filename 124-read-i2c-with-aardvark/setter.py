#!/usr/bin/env python

import os
import sys

from helpers import *

from aardvark_py import *

I2C_ADDR_OF_EEPROM = 0x50

def soft_reset(handle):
    value = read_phy_reg(aardvark_handle, 0)
    value = value | (1 << 15)
    write_phy_reg(aardvark_handle, 0, value)

def set_hwmode(handle, mode):
    value = read_phy_reg(aardvark_handle, 27)
    value = (value & 0xFFF0) | mode
    write_phy_reg(aardvark_handle, 27, value)

if __name__ == '__main__':
    aardvark_handle = open_aardvark()
    if aardvark_handle < 0:
        print(f"error opening aardvark '{aa_status_string(aardvark_handle)}'")
        sys.exit(1)

    # supported bitrates: 100, 200, 307, 400, 500, 615, 727, 800
    aa_i2c_bitrate(aardvark_handle, 100)

    #write_phy_reg(aardvark_handle, 24, 0xAAAA)
    #write_phy_reg(aardvark_handle, 25, 0xAAAA)

    #sys.exit(0)

    if not sys.argv[1:]:
        print('ERROR: supply arg')

    command = sys.argv[1]

    if 0:
        write_phy_reg(aardvark_handle, 27, 0x9084)
        write_phy_reg(aardvark_handle, 0x00, 0xA100)
        write_phy_reg(aardvark_handle, 0x10, 0x0011)
        write_phy_reg(aardvark_handle, 0x00, 0xA100)

    if 0:
        write_phy_reg(aardvark_handle, 27, 0x908F)
        write_phy_reg(aardvark_handle, 0x00, 0x8100)
        write_phy_reg(aardvark_handle, 0x10, 0x0411)
        write_phy_reg(aardvark_handle, 0x00, 0x8100)

    if 0:
        write_phy_reg(aardvark_handle, 27, 0x908F)
        write_phy_reg(aardvark_handle, 0x00, 0x8100)
        write_phy_reg(aardvark_handle, 0x10, 0x0411)
        write_phy_reg(aardvark_handle, 0x00, 0x8100)
        write_phy_reg(aardvark_handle, 0x1d, 0x0012)
        write_phy_reg(aardvark_handle, 0x1e, 0x8920)

    if command == 'mode0':
        set_hwmode(aardvark_handle, 0b0100) # SGMII without Clock with SGMII Auto-Neg to copper
        soft_reset(aardvark_handle)

    if command == 'mode1':
        set_hwmode(aardvark_handle, 0b1000) # 1000BASE-X without Clock with 1000BASE-X Auto-Neg to copper (GBIC)
        soft_reset(aardvark_handle)

    # works!?
    if command == 'mode2':
        set_hwmode(aardvark_handle, 0b1100) # 1000BASE-X without Clock without 1000BASE-X Auto-Neg to copper
        soft_reset(aardvark_handle)

    if command == 'test':
        # enable sgmii mode
        read_phy_reg(aardvark_handle, 27)
        write_phy_reg(aardvark_handle, 27, 0x9084)
        
        # advertise 1000base-t full/half-duplex
        #write_phy_reg(aardvark_handle, 0x09, 0x0f00)

        # software reset with other bits
        read_phy_reg(aardvark_handle, 0)
        write_phy_reg(aardvark_handle, 0x00, 0x8140)
        
        # advertise 100/10base-t full/half-duplex
        #write_phy_reg(aardvark_handle, 0x04, 0x0de1)
        # software reset with other bits
        #write_phy_reg(aardvark_handle, 0x00, 0x9140)


    if command == 'serial_bypass':
        value = read_phy_reg(aardvark_handle, 27)
        print(f'old value: 0x{value:04X}')

        value = value ^ (1 << 12)
        print(f'new value: 0x{value:04X}')

        write_phy_reg(aardvark_handle, 27, value)

        value = read_phy_reg(aardvark_handle, 27)
        print(f'check value: 0x{value:04X}')

        soft_reset(aardvark_handle)

    if command == 'led':
        value = read_phy_reg(aardvark_handle, 24)
        print(f'old value: 0x{value:04X}')
        if value == 0x4100:
            print(f'setting to 0xAAAA')
            write_phy_reg(aardvark_handle, 24, 0xAAAA)
        else:
            print(f'setting to 0x4100')
            write_phy_reg(aardvark_handle, 24, 0x4100)

    if command == 'setup':
        # enable sgmii mode
        write_phy_reg(aardvark_handle, 27, 0x9084)
        # advertise 1000base-t full/half-duplex
        write_phy_reg(aardvark_handle, 0x09, 0x0f00)
        # software reset with other bits
        write_phy_reg(aardvark_handle, 0x00, 0x8140)
        # advertise 100/10base-t full/half-duplex
        write_phy_reg(aardvark_handle, 0x04, 0x0de1)
        # software reset with other bits
        write_phy_reg(aardvark_handle, 0x00, 0x9140)

        # try to set bypass of serial autonegotiation
        for try_num in range(4):
            value = read_phy_reg(aardvark_handle, 27)
            print(f'old value: 0x{value:04X}')

            value = value ^ (1 << 12)
            print(f'new value: 0x{value:04X}')

            write_phy_reg(aardvark_handle, 27, value)

            value = read_phy_reg(aardvark_handle, 27)
            print(f'check value: 0x{value:04X}')

            if value & (1 << 12):
                break
            else:
                print(f'did not check! trying to set again!')
                time.sleep(.4)
        else:
            print('ERROR: setting did not stick!')
            sys.exit(-1)

        soft_reset(aardvark_handle)

    if command == 'reset':
        soft_reset(aardvark_handle)

    if 0:
        write_phy_reg(aardvark_handle, 0x16, 0x0001)
        write_phy_reg(aardvark_handle, 0x00, 0x8140)
        write_phy_reg(aardvark_handle, 0x16, 0x0000)

