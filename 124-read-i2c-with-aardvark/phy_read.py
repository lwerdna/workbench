#!/usr/bin/env python

import os
import sys

from helpers import *

from aardvark_py import *

I2C_ADDR_OF_EEPROM = 0x50

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

    aardvark_handle = open_aardvark()
    if aardvark_handle < 0:
        print(f"error opening aardvark '{aa_status_string(aardvark_handle)}'")
        sys.exit(1)

    # supported bitrates: 100, 200, 307, 400, 500, 615, 727, 800
    aa_i2c_bitrate(aardvark_handle, 100)

    data = read_phy(aardvark_handle, addr, length)
    data = data.tobytes()

    if not data:
        print('ERROR: no data')
        sys.exit(-1)

    print(hexdump(data))

    regs = [(data[i]<<8)|data[i+1] for i in range(0,64,2)]

    names = [
        'Control Register', 'Status Register',
        'PHY identifier', 'PHY identifier',
        'Auto-Neg Advertisement Register', 'Link Partner Ability Register', 'Auto-Neg Expansion Register',
        'Next Page Transmit Register', 'Link Partner Next Page Register',
        '1000BASE-T Control Register', '1000BASE-T Status Register',
        'Reserved', 'Reserved', 'Reserved', 'Reserved',
        'Extended Status Register',
        'PHY Specific Control Register', 'PHY Specific Status Register',
        'Interrupt Enable Register', 'Interrupt Status Register',
        'Extended PHY Specific Control Register',
        'Receive Error Counter Register',
        'Extended Address Register',
        'Global Status Register', 'LED Control Register', 'Manual LED Override Register', 'Extended PHY Specific Control 2 Register', 'Extended PHY Specific Status Register', 'Dunno', 'Extended Address', 'Dunno', 'Reserved']

    assert len(names) == 32
    for i, name in enumerate(names):
        print(f'register[{i:02d}] {name:42} 0x{regs[i]:04X}')

    def bit(val, idx):
        return 1 if (val & (1<<idx)) else 0

    #--------
    # CONTROL REGISTER, REG0
    #--------
    reg = regs[0]
    vals = []
    print(f'Control Register (0): 0x{reg:04X}')
    if reg & (1<<15): print('  reset')
    if reg & (1<<14): print('  loopback')
    #if reg & (1<<13): print('  Speed Select (LSB)')
    if bit(reg, 12):
        print('  autoneg enabled')
    else:
        print('  autoneg disabled')

    if reg & (1<<11): print('  power Down')
    if reg & (1<<10): print('  isolate')
    if reg & (1<<9): print('  restart copper autoneg')
    if reg & (1<<8): print('  copper duplex mode')
    if reg & (1<<7): print('  Collision Test')
    #if reg & (1<<6): print('  Speed Selection (MSB)')
    if reg & (1<<5): print('  reserved b5')
    if reg & (1<<4): print('  reserved b4')
    if reg & (1<<3): print('  reserved b3')
    if reg & (1<<2): print('  reserved b2')
    if reg & (1<<1): print('  reserved b1')
    if reg & (1<<0): print('  reserved b0')
    speed = (bit(reg, 6) << 1) | bit(reg, 13)
    if speed == 0b11:
        print('  speed: reserved')
    elif speed == 0b10:
        print('  speed: 1000 Mbps')
    elif speed == 0b01:
        print('  speed: 100 Mbps')
    elif speed == 0b00:
        print('  speed: 10 Mbps')

    #--------
    # STATUS REGISTER, REG1
    #--------
    reg = regs[1]
    vals = []
    print(f'Status Register (1): 0x{reg:04X}')
    if bit(reg, 15):
        print('  able to perform 100BASE-T4')
    if bit(reg, 14):
        print('  able to perform full-duplex 100BASE-X')
    if bit(reg, 13):
        print('  able to perform half-dplex 100BASE-X')
    if bit(reg, 12):
        print('  able to perform full-duplex 10BASE-T')
    if bit(reg, 11):
        print('  able to perform half-duplex 10BASE-T')
    if bit(reg, 8):
        print('  extended status in reg 15')
    if bit(reg, 6):
        print('  phy accepts mgmt frames with preamble suppressed')
    if bit(reg, 5):
        print('  autoneg process complete')
    else:
        print('  autoneg process incomplete')
    if bit(reg, 4):
        print('  remote fault condition detected')
    if bit(reg, 3):
        print('  phy able to perform autoneg')
    if bit(reg, 2):
        print('  copper link status (delayed): UP')
    else:
        print('  copper link status (delayed): DOWN')
    if bit(reg, 1):
        print(' jabber detect')

    reg = regs[17]
    vals = []
    print(f'PHY Specific Status Register (17) - Copper: 0x{reg:04X}')
    if bit(reg, 10):
        print('  Link (real time): UP')
    else:
        print('  Link (real time): DOWN')

    reg = regs[27]
    print(f'Extended PHY Specific Status Register (27): 0x{reg:04X}')

    word = ['disable', 'enable'][bit(reg, 15)]
    print(f'  Fiber/Copper Auto Selection: {word}d')

    word = ['copper', 'fiber'][bit(reg, 13)]
    print(f'  Fiber/Copper resolution: {word} link')

    word = ['disable', 'enable'][bit(reg, 12)]
    print(f'  Serial Interface Autoneg bypass: {word}d')

    word = ['link up due to regular fiber autoneg', 'link up because bypass mode timer expired and fiber Autoneg was bypassed'][bit(reg, 11)]
    print(f'  Serial Interface Autoneg bypass status: {word}')

    word = ['active high', 'active low'][bit(reg, 10)]
    print(f'  Interrupt Polarity: {word}')

    word = ['enable', 'disable'][bit(reg, 9)]
    print(f'  automatic medium register selection: {word}d')

    tmp = reg & 0b111100000
    print(f'  DTE detect status drop hysteresis: {tmp*5} seconds')

    word = ['does not need', 'needs'][bit(reg, 4)]
    print(f'  DTE power status: {word} DTE power')
        
    tmp = reg & 0b1111
    print('********')
    if tmp == 0b0000: print('  HWCFG_MODE: SGMII with Clock with SGMII Auto-Neg to copper')
    if tmp == 0b0100: print('  HWCFG_MODE: SGMII without Clock with SGMII Auto-Neg to copper')
    if tmp == 0b1000: print('  HWCFG_MODE: 1000BASE-X without Clock with 1000BASE-X Auto-Neg to copper (GBIC)')
    if tmp == 0b1100: print('  HWCFG_MODE: 1000BASE-X without Clock without 1000BASE-X Auto-Neg to copper')
    if tmp == 0b0001: print('  HWCFG_MODE: Reserved')
    if tmp == 0b1001: print('  HWCFG_MODE: Reserved')
    if tmp == 0b1001: print('  HWCFG_MODE: RTBI to Copper')
    if tmp == 0b1101: print('  HWCFG_MODE: TBI to copper')
    if tmp == 0b0010: print('  HWCFG_MODE: Reserved')
    if tmp == 0b0110: print('  HWCFG_MODE: RGMII to SGMII')
    if tmp == 0b1010: print('  HWCFG_MODE: Reserved')
    if tmp == 0b1110: print('  HWCFG_MODE: GMII to SGMII')
    if tmp == 0b0011: print('  HWCFG_MODE: RGMII to Fiber')
    if tmp == 0b0111: print('  HWCFG_MODE: GMII to Fiber')
    if tmp == 0b1011: print('  HWCFG_MODE: RGMII/Modified MII to Copper')
    if tmp == 0b1111: print('  HWCFG_MODE: GMII to copper')
    print('********')


