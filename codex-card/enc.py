#!/usr/bin/env python

def get_keystream(key):
    result = []
    for i in range(15):
        result.append(key)
        key = (key*13 + 37) % 256
    return result

def try_key(key):
    stream = get_keystream(key)
    flag = [0x3c, 0xf7, 0xbf, 0x3c, 0xd9, 0x53, 0x49, 0x57, 0x33, 0x27, 0x68, 0xba, 0x70, 0x28, 0x65]

    for i in range(len(flag)):
        flag[i] = ((flag[i]-3) % 256) ^ stream[i]

    return ''.join(chr(x) for x in flag)

for k in range(256):
    result = try_key(k)
    print(f'for key {k}: {result}')


