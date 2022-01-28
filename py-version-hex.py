#!/usr/bin/env python

# https://docs.python.org/3/c-api/apiabiversion.html

import os, sys, re, pprint

if __name__ == '__main__':
    value = int(sys.argv[1], 16)

    PY_MAJOR_VERSION = (0b11111111000000000000000000000000 & value) >> 24
    PY_MINOR_VERSION = (0b00000000111111110000000000000000 & value) >> 16
    PY_MICRO_VERSION = (0b00000000000000001111111100000000 & value) >> 8
    PY_RELEASE_LEVEL = (0b00000000000000000000000011110000 & value) >> 4
    PY_RELEASE_SERIAL = (0b00000000000000000000000000001111 & value)

    vstring = '%d.%d.%d' % (PY_MAJOR_VERSION, PY_MINOR_VERSION, PY_MICRO_VERSION)

    if PY_RELEASE_LEVEL in [0xA, 0xB, 0xC, 0xF]:
        vstring += '%x' % PY_RELEASE_LEVEL

    if PY_RELEASE_SERIAL:
        vstring += str(PY_RELEASE_SERIAL)

    print(vstring)
