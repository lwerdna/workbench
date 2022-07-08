#!/usr/bin/env python

# update to python3

FNAME = b'test.txt'
PLAINTEXT = b'Hello, world!\n'
PASSPHRASE = b'TestPassphrase'

import os
import sys
from hashlib import sha1
from struct import pack
from base64 import b64encode
from cast128 import cast128_encrypt_block

def strxor(a, b):
    chunk = min(len(a), len(b))
    result = b''
    for i in range(chunk):
        result += pack('B', a[i] ^ b[i])
    return result

def create_pkt(body, tagid):
    tag_byte = 0x80                                # b7=1 (always) b6=0 (old fmt)
    tag_byte |= (tagid << 2)                       # b5..b2

    length_bytes = ''
    if len(body) < 256:
        tag_byte |= 0                              # length type = 0 (1 byte length)
        length_bytes = pack('>B', len(body))       #
    elif len(body) < 65536:
        tag_byte |= 1
        length_bytes = pack('>H', len(body))
    elif len(body) < 1048576:
        tag_byte |= 2
        length_bytes = pack('>I', len(body))
    else:
        raise Exception('too large')
    
    pkt_hdr = pack('B', tag_byte) + length_bytes   # hdr = tag byte + length bytes
    
    return pkt_hdr + body                          # add hdr

def create_pkt3(salt):
    body = b'\x04'                                 # version
    body += b'\x03'                                # block algo: CAST5
    body += b'\x03'                                # s2k id: Iterated+Salted
    body += b'\x02'                                # hash id: sha1
    body += salt
    body += b'\x60'                                # count (decodes to 65536)
    return create_pkt(body, 3)

def create_pkt9(ptext, passphrase, salt):
    msg = b''                                      # create hash input
    while len(msg) < 65536:
        msg = msg + salt + passphrase
    msg = msg[0:65536]
    
    m = sha1()                                     # hash it
    m.update(msg)
    digest = m.digest()

    key = digest[0:16]                             # CAST5 key is 16 bytes of hash

    # encrypt with OpenPGP CFB Mode (see 13.9)
    prefix = os.urandom(8)

    FR = b'\x00'*8
    FRE = cast128_encrypt_block(FR, key)
    ctext = strxor(prefix, FRE)

    FR = ctext
    FRE = cast128_encrypt_block(FR, key)
    ctext += strxor(prefix[6:8], FRE[0:2])

    FR = ctext[2:10]
    while ptext:
        FRE = cast128_encrypt_block(FR, key)
        FR = strxor(ptext[0:8], FRE)
        ctext += FR
        ptext = ptext[8:]

    return create_pkt(ctext, 9);

def create_pkt11(msg):
    body = b'\x62'                                 # 'b' format (binary)
    body += pack('B', len(FNAME))                  # filename len
    body += FNAME                                  # filename
    body += b'\x00'*4                              # date
    body += msg
    return create_pkt(body, 11)

if __name__ == '__main__':
    pkt11 = create_pkt11(PLAINTEXT)

    salt = os.urandom(8)
    pkt9 = create_pkt9(pkt11, PASSPHRASE, salt)
    #print('pkt9: ', pkt9.hex())

    pkt3 = create_pkt3(salt)
    #print('pkt3: ', pkt3.hex())
    
    print(pkt3 + pkt9)
