#!/usr/bin/env python3

guts = None
with open('hello', 'rb') as fp:
    guts = fp.read()

before = 6 * b'\xc0\x46'

after = \
b'\xbe\xbf' + \
b'\xaf\xf3\x00\x80' + \
b'\xaf\xf3\x00\x80' + \
b'\xf8\xe7'

assert len(before) == len(after)

guts = guts.replace(before, after)

with open('hello-interesting', 'wb') as fp:
    fp.write(guts)
