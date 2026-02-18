#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()

    if not sys.argv[2:]:
        print('ERROR: supply register and value to write')

    arg = sys.argv[1]
    addr = int(arg, 16 if arg.startswith('0x') else 10)
    arg = sys.argv[2]
    value = int(arg, 16 if arg.startswith('0x') else 10)

    value = write_reg(ser, addr, value)

    ser.close()

