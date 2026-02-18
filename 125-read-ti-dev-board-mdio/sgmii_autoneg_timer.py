#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()
    value = read_reg(ser, 0x31)
    ser.close()

    ser = connect()
    value2 = value & 0xFF9F
    print(f'  0x{value:04X} -> 0x{value2:04X}')
    write_reg(ser, 0x31, value2)
    ser.close()
