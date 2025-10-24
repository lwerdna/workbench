#!/usr/bin/env python

import sys
import time
import array
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

def print_power_state(handle):
    t = aa_target_power(handle, AA_TARGET_POWER_QUERY)
    if t == AA_TARGET_POWER_NONE:
        print('current power: OFF')
    elif t == AA_TARGET_POWER_BOTH:
        print('current power: ON')
    else:
        raise Exception('unknown power state: {t}')

def config_spi(handle):
    result = aa_spi_bitrate(handle, 125)
    assert result == 125

    # polarity
    #   AA_SPI_POL_FALLING_RISING - idle clock is high
    #   AA_SPI_POL_RISING_FALLING - idle clock is low (default according to Logic2)
    # phase
    #   AA_SPI_PHASE_SAMPLE_SETUP - sample on leading edge, setup on trailing edge (default, I think, according to Logic2)
    #   AA_SPI_PHASE_SETUP_SAMPLE - setup on leading edge, sample on trailing edge
    # bitorder
    #   AA_SPI_BITORDER_MSB - most significant bit first (default, according to Logic2)
    #   AA_SPI_BITORDER_LSB - least significant bit first
    result = aa_spi_configure(handle, polarity=AA_SPI_POL_RISING_FALLING, phase=AA_SPI_PHASE_SAMPLE_SETUP, bitorder=AA_SPI_BITORDER_MSB)
    assert result == AA_OK

    result = aa_spi_slave_disable(handle)
    assert result == AA_OK

    result = aa_spi_master_ss_polarity(handle, AA_SPI_SS_ACTIVE_LOW)
    assert result == AA_OK

def read_jedec(handle):
    in_data = array('B', [0x9f, 0x00, 0x00, 0x00])
    out_data = array('B', [0xAA, 0xBB, 0xCC, 0xDD])
    (status, data) = aa_spi_write(handle, in_data, out_data)
    if status < 0:
        assert False
    print(f'wow: {out_data}')

if __name__ == '__main__':
    handle = open_aardvark()
    time.sleep(1)
    config_spi(handle)
    read_jedec(handle)

    print('done')
