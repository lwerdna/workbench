#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()
    value = read_reg(ser, 0x1d5)
    ser.close()

    ser = connect()
    value2 = value ^ (1 << 1)
    write_reg(ser, 0x1d5, value2)
    ser.close()
