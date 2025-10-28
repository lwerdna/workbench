#!/usr/bin/env python

import sys
import time
import struct

from helpers import *

# pip install aardvark_py
from aardvark_py import *


if __name__ == '__main__':
    handle = open_aardvark()

    if power_get(handle) == 'on':
        power_off(handle)
    else:
        power_on(handle)

    print('done')
