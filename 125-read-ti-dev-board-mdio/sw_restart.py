#!/usr/bin/env python

import os
import sys

from helpers import *

if __name__ == '__main__':
    ser = connect()
    write_reg(ser, 0x1f, 0x4000)
    ser.close()
