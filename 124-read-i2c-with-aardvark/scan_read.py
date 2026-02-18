#!/usr/bin/env python

import os
import sys

from aardvark_py import *

from helpers import *

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


bitrates = [100, 200, 307, 400, 500, 615, 727, 800]
bitrate_khz = bitrates[0]

slave_addr = 10

flags = AA_I2C_NO_FLAGS
# AA_I2C_10_BIT_ADDR | AA_I2C_COMBINED_FMT | AA_I2C_NO_STOP | AA_I2C_SIZED_READ | AA_I2C_SIZED_READ_EXTRA1

# -----------------

data_out = array('B', [1, 2, 3, 4])

# -----------------------------------------------------------------------------

#
aardvark_handle = open_aardvark()
if aardvark_handle < 0:
    print(f"error opening aardvark '{aa_status_string(aardvark_handle)}'")
    sys.exit(1)

aa_i2c_bitrate(aardvark_handle, bitrate_khz)

# Full API at:
# https://www.totalphase.com/support/articles/200468316-aardvark-i2c-spi-host-adapter-user-manual/
# aa_i2c_pullup()
# aa_i2c_free_bus()
# aa_i2c_bus_timeout()
# aa_i2c_bitrate()
# aa_i2c_read()
# aa_i2c_read_ext()
# aa_i2c_write()
# aa_i2c_write_ext()
# aa_i2c_write_read()

#status, data_in = aa_i2c_read(aardvark_handle, slave_addr, flags, 4)
if 0:
    status, data_in = aa_i2c_read(aardvark_handle, 0x50, flags, 256)
    data_in = data_in.tobytes()
    print(f'got raw data: {repr(data_in)}')
    print(f'got raw data: {data_in.hex()}')

    if status < 0:
        print(f"fail reading data ({aa_status_string(status)})")
    else:
        if not data_in:
            print(f'ERROR (kinda): received 0 bytes')
        else:
            print(f"data {data_in} received on i2c")

if 0:
    # scan for register address
    for reg_controller in range(0b10000000):
        # write register address
        reg_addr = array('B', [0, 9])
        print(f'writing {reg_addr} to 0x{reg_controller:X}')
        aa_i2c_write(aardvark_handle, reg_controller, flags, reg_addr)

        # read and hope for something
        print(f'reading from 0x{reg_controller:X}')
        status, data = aa_i2c_read(aardvark_handle, reg_controller, flags, 2)
        data = data.tobytes()

        if status > 0:
            print(f'reg_controller=0x{reg_controller:X} data={data.hex()}')

if 1:
    print('==== 7-bit addressing, raw i2c_read ====')
    # scan for register address
    for addr in range(0b10000000):
        # read and hope for something
        print(f'reading from 0x{addr:X}')
        status, data = aa_i2c_read(aardvark_handle, addr, flags, 2)
        data = data.tobytes()

        if status > 0:
            print(f'0x{addr:X}: {data.hex()}')

if 1:
    print('==== 7-bit addressing, write-address-then-read ====')
    # scan for register address
    for device in range(0b10000000):
        # read and hope for something
        addr = 0
        length = 2
        print(f'reading {length} bytes from device 0x{device:X}, address 0')
        data = general_read(aardvark_handle, addr, length, device)

        if data:
            data = data.tobytes()
            print(f'0x{addr:X}: {data.hex()}')

if 0:
    print('==== 10-bit addressing ====')
    # scan for register address
    for addr in range(0b10000000000):
        # read and hope for something
        print(f'reading from 0x{addr:X}')
        status, data = aa_i2c_read(aardvark_handle, addr, AA_I2C_10_BIT_ADDR, 2)
        data = data.tobytes()

        if status > 0:
            print(f'0x{addr:X}: {data.hex()}')

###############################################################################
# CLEANUP
aa_close(aardvark_handle)

