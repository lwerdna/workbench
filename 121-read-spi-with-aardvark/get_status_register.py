#!/usr/bin/env python

import sys
import time
import array
import struct

from helpers import *

# pip install aardvark_py
from aardvark_py import *

if __name__ == '__main__':
    handle = open_aardvark()

    print(f'activate logic analyzer!')
    time.sleep(2)

    print(f'doing it!')
    config_spi(handle)
    rdsr(handle)

    print('done')
