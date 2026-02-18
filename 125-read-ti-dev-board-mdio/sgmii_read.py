#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()

    reg = read_reg(ser, 0x10)
    print(f'0010: 0x{reg:04X} // PHY Control Register (PHYCR)')
    print('  SGMII_EN: %d' % bit(reg, 11))

    reg = read_reg(ser, 0x14)
    print(f'0014: 0x{reg:04X} // Configuration Register 2 (CFG2)')
    print('  SGMII_AUTONEG_EN: %d' % bit(reg, 7))

    reg = read_reg(ser, 0x31)
    print(f'0031: 0x{reg:04X} // Configuration Register 4 (CFG4)')
    value = (bit(reg, 6)<<1)|(bit(reg, 5))
    print(f'  SGMII_AUTONEG_TIMER: %d (%s)' % (value, ['16ms', '2us', '800us', '11ms'][value]))

    reg = read_reg(ser, 0x37)
    print(f'0037: 0x{reg:04X} // SGMII Auto-Negotiation Status (SGMII_ANEG_STS)')
    print('  SGMII_PAGE_RX: %d' % bit(reg, 1))
    print('  SGMII_AUTONEG_COMPLETE: %d' % bit(reg, 0))

    reg = read_reg(ser, 0xd3)
    print(f'00D3: 0x{reg:04X} // SGMII Control Register 1 (SGMIICTL1)')
    print('  SGMII_TYPE: %d (0=4-wire mode, 1=6-wire mode)' % bit(reg, 14))

    reg = read_reg(ser, 0x1d5)
    print(f'00D3: 0x{reg:04X} // Programmable Gain (PROG_GAIN)')
    print('  SGMII_TX_POL_IN: %d (0=normal polarity, 1=inverted polarity)' % bit(reg, 1))
    print('  SGMII_RX_POL_IN: %d (0=normal polarity, 1=inverted polarity)' % bit(reg, 0))

    ser.close()

