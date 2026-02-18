#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()

    if not sys.argv[1:]:
        print('ERROR: supply register to read')

    arg = sys.argv[1]
    addr = int(arg, 16 if arg.startswith('0x') else 10)

    value = read_reg(ser, addr)
    print(f'{addr:04X}: 0x{value:04X}')

    ser.close()

