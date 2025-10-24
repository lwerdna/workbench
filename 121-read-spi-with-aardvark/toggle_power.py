#!/usr/bin/env python

import sys
import time
import struct

# pip install aardvark_py
from aardvark_py import *

def open_aardvark():
    num, ports = aa_find_devices(16)
    if num <= 0:
        raise RuntimeError('No Aardvark adapters found')
    port = ports[0]
    print(f'aardvark port: {port}')
    handle = aa_open(port)
    if handle < 0:
        raise RuntimeError('aa_open failed: {handle}')
    print(f'aardvark handle: {handle}')
    return handle

if __name__ == '__main__':
    handle = open_aardvark()

    t = aa_target_power(handle, AA_TARGET_POWER_QUERY)
    if t == AA_TARGET_POWER_NONE:
        print('powering on')
        aa_target_power(handle, AA_TARGET_POWER_BOTH)
    elif t == AA_TARGET_POWER_BOTH:
        print('powering off')
        aa_target_power(handle, AA_TARGET_POWER_NONE)
    else:
        raise Exception('unknown power state: {t}')

    print('done')
