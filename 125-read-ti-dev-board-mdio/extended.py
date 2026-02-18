#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()

    reg = read_reg(ser, REG_ADDR_REGCR);
    print(f'000D: 0x{reg:04X} // (EXTENDED) Register Control Register (REGCR)')
    Function = (reg >> 14) & 0x3
    if Function == 0:
        print('  Function: 0 (writes to ADDAR set the extended address)')
    elif Function == 1:
        print('  Function: 1 (R/W to ADDAR returns data from extended address)')
    elif Function == 2:
        print('  Function: 2 (R/W to ADDAR accesses data, increments on R+W)')
    elif Function == 3:
        print('  Function: 3 (R/W to ADDAR accesses data, increments on W)')

    reg = read_reg(ser, REG_ADDR_ADDAR);
    print(f'000E: 0x{reg:04X} // (EXTENDED) Address or Data Register (ADDAR)')
    if Function == 0:
        print('  (this is the MMD DEVAD address)')
    else:
        print('  (this is the MMD DEVAD data)')

    ser.close()

