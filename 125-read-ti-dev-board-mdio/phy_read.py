#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()

    reg = read_reg(ser, 0);
    print(f'0000: 0x{reg:04X} // Basic Mode Control Register (BMCR)')
    #print('  RESET: %d' % bit(reg, 15))
    #print('  LOOPBACK: %d' % bit(reg, 14))
    print('  AUTO-NEG ENABLE: %d' % bit(reg, 12))
    #print('  POWER DOWN: %d' % bit(reg, 11))
    #print('  isolate: %d' % bit(reg, 10))
    #print('  RESTART AUTO-NEG: %d' % bit(reg, 9))
    print('  duplex mode: %d (1==full, 0==half)' % bit(reg, 8))
    #print('  collision test: %d' % bit(reg, 7))
    ss = ['10Mbps', '100Mbps', '1000Mbps', 'Reserved'][(bit(reg, 6)<<1)|bit(reg, 13)]
    print(f'  speed selection: {ss}')

    reg = read_reg(ser, 1);
    print(f'0001: 0x{reg:04X} // Basic Mode Status Register (BMSR)')
    #print('  100BASE-T4 capable: %d' % bit(reg, 15))
    #print('  100BASE-TX FULL DUPLEX: %d' % bit(reg, 14))
    #print('  100BASE-TX HALF DUPLEX: %d' % bit(reg, 13))
    #print('  10BASE-Te FULL DUPLEX: %d' % bit(reg, 12))
    #print('  10BASE-Te HALF DUPLEX: %d' % bit(reg, 11))
    #print('  100BASE-T2 HALF DUPLEX: %d' % bit(reg, 9))
    #print('  MF PREAMBLE SUPRESSION: %d' % bit(reg, 6))
    print('  AUTO-NEG COMPLETE: %d' % bit(reg, 5))
    print('  REMOTE FAULT: %d' % bit(reg, 4))
    print('  AUTO-NEG ABILITY: %d' % bit(reg, 3))
    print('  LINK STATUS: %d' % bit(reg, 2))
    #print('  JABBER DETECT: %d' % bit(reg, 1))
    print('  EXTENDED CAPABILITY: %d' % bit(reg, 1))

    reg = read_reg(ser, 2);
    print(f'0002: 0x{reg:04X} // PHY Identifier Register #1 (PHYIDR1)')

    reg = read_reg(ser, 3);
    print(f'0003: 0x{reg:04X} // PHY Identifier Register #2 (PHYIDR2)')

    reg = read_reg(ser, 4);
    print(f'0004: 0x{reg:04X} // Auto-Negotiation Advertisement Register (ANAR)')

    reg = read_reg(ser, 0xF)
    print(f'000F: 0x{reg:04X} // 1000BASE-T Status Register (1KSCR)')
    print('  1000BASE-X FULL DUPLEX SUPPORT: %d' % bit(reg, 15))
    print('  1000BASE-X FULL DUPLEX SUPPORT: %d' % bit(reg, 14))
    print('  1000BASE-T FULL DUPLEX SUPPORT: %d' % bit(reg, 13))
    print('  1000BASE-T FULL DUPLEX SUPPORT: %d' % bit(reg, 12))

    reg = read_reg(ser, 0x10)
    print(f'0010: 0x{reg:04X} // PHY Control Register (PHYCR)')
    print('  SGMII_EN: %d' % bit(reg, 11))
    print('  FORCE_LINK_GOOD: %d' % bit(reg, 10))
    print('  POWER_SAVE_MODE: %d' % ((bit(reg, 9)<<1)|bit(reg, 8)))

    reg = read_reg(ser, 0x11)
    print(f'0011: 0x{reg:04X} // PHY Status Register (PHYSTS)')
    SpeedSelection = (reg>>14) & 3
    SpeedSelectionStr = ['10Mbps', '100Mbps', '1000Mbps', 'Reserved'][SpeedSelection]
    print('  SPEED SELECTION: %d (%s)' % (SpeedSelection, SpeedSelectionStr))
    print('  DUPLEX MODE: %d' % bit(reg, 13))
    print('  PAGE RECEIVED: %d' % bit(reg, 12))
    print('  SPEED DUPLEX RESOLVED: %d' % bit(reg, 11))
    print('  LINK_STATUS: %d' % bit(reg, 10))
    print('  MDI_X_MODE_CD: %d' % bit(reg, 9))
    print('  MDI_X_MODE_AB: %d' % bit(reg, 8))

    reg = read_reg(ser, 0x14)
    print(f'0014: 0x{reg:04X} // Configuration Register 2 (CFG2)')
    print('  SGMII_AUTONEG_EN: %d' % bit(reg, 7))

    reg = read_reg(ser, 0x15)
    print(f'0015: 0x{reg:04X} // Receiver Error Counter Register (RECR)')

    reg = read_reg(ser, 0x37)
    print(f'0037: 0x{reg:04X} // SGMII Auto-Negotiation Status (SGMII_ANEG_STS)')
    print('  SGMII_PAGE_RX: %d' % bit(reg, 1))
    print('  SGMII_AUTONEG_COMPLETE: %d' % bit(reg, 0))

    #reg = read_reg(ser, 0x10);
    #print(f'Auto-Negotiation Advertisement Register (ANAR): 0x{reg:04X}')

#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))
#    print('  reset: %d' % bit(reg, 0))


    ser.close()

