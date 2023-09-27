#!/usr/bin/env python3

guts = None
with open('hello', 'rb') as fp:
    guts = fp.read()

# move r8, r8
before = 6 * b'\xc0\x46'

# be bf       ittt lt
# af f3 00 80 nop.w
# af f3 00 80 nop.w
# f8 e7       b top
after = \
b'\xbe\xbf' + \
b'\xaf\xf3\x00\x80' + \
b'\xaf\xf3\x00\x80' + \
b'\xf8\xe7'

assert len(before) == len(after)

guts = guts.replace(before, after)

with open('hello-interesting', 'wb') as fp:
    fp.write(guts)
