#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()
    value = read_reg(ser, 0x14)
    print(f'0014: 0x{value:04X} // Configuration Register 2 (CFG2)')
    print('  SGMII_AUTONEG_EN: %d' % bit(value, 7))
    ser.close()

    ser = connect()
    value2 = value ^ (1 << 7)
    print(f'  0x{value:04X} -> 0x{value2:04X}')
    write_reg(ser, 0x14, value2)
    ser.close()

    ser = connect()
    value = read_reg(ser, 0x14)
    print(f'0014: 0x{value:04X} // Configuration Register 2 (CFG2)')
    print('  SGMII_AUTONEG_EN: %d' % bit(value, 7))
    ser.close()
