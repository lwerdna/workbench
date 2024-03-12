#!/usr/bin/env python

from Crypto.Cipher import ARC4

# test vectors from https://en.wikipedia.org/wiki/RC4
assert ARC4.new(b'Key').encrypt(b'Plaintext') == b'\xbb\xf3\x16\xe8\xd9\x40\xaf\x0a\xd3'
assert ARC4.new(b'Wiki').encrypt(b'pedia') == b'\x10\x21\xBF\x04\x20'
assert ARC4.new(b'Secret').encrypt(b'Attack at dawn') == b'\x45\xA0\x1F\x64\x5F\xC3\x5B\x38\x35\x52\x54\x4B\x9B\xF5'

chars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'

ctext = bytes.fromhex('f473f13024b54f3558f1624855')

for a in chars:
    for b in chars:
        for c in chars:
            for d in chars:
                key = (a+b+c+d).encode('utf-8')
                cipher = ARC4.new(key)
                ptext = cipher.encrypt(ctext)
                #print(f'key={key} ptext={ptext}')

                if ptext[0] >= 32 and ptext[0] <= 126:
                    if b'lag' in ptext:
                        print(f'key={key} ptext={ptext}')
