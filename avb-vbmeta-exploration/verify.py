#!/usr/bin/env python

# exercise the signature in this AVB meta partition

import sys
import hashlib

from helpers import *

info = read(open('./vbmeta.img', 'rb'))

# lookup standard values depending on algorithm type
match info['AvbVBMetaImageHeader']['algorithm_type']:
    case 1: # SHA256_RSA2048
        R = 2**2048
        padding = list(b'\x00\x01' + b'\xff'*202 + b'\x00\x30\x31\x30\x0d\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x01\x05\x00\x04\x20') # padding_RSA2048_SHA256
        sig_size = 256
    case 2: # SHA256_RSA4096
        R = 2**4096
        padding = list(b'\x00\x01' + b'\xff'*458 + b'\x00\x30\x31\x30\x0d\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x01\x05\x00\x04\x20') # padding_RSA4096_SHA256
        sig_size = 512
    case _:
        raise Exception('unsupported')

print(f'R = 0x{R:X}')
print(f'padding = {bytes_to_num(padding):X}')

N_data = info['Auxiliary']['AvbRSAPublicKey']['n']
N = bytes_to_num(N_data)
print(f'N = 0x{N:x}')

# verify n0inv
n0inv = info['Auxiliary']['AvbRSAPublicKey']['AvbRSAPublicKeyHeader']['n0inv']
print(f'n0inv = 0x{n0inv:x}')
n0 = bytes_to_num(N_data[-4:]) # n[0], the lowest 32-bit dword of N
print(f'n0 = 0x{n0:x}')
assert n0 * n0inv % 0x100000000 == -1 + 0x100000000

# verify RR
RR = bytes_to_num(info['Auxiliary']['AvbRSAPublicKey']['rr'])
print(f'RR = 0x{RR:x}')
assert pow(R, 2, N) == RR

# the auxiliary modulus R should be coprime with N
assert gcd(N, R) == 1

# compute, verify R^-1 (mod N)
R_inv = multiplicative_inverse(R, N)
assert R * R_inv % N == 1

# get, verify signature
sig_data = info['Authentication']['signature']
assert len(sig_data) == sig_size
signature = bytes_to_num(sig_data)
print(f'signature = 0x{signature:x}')

hash_data = info['Authentication']['hash']
print(f'hash = {bytes_to_num(hash_data):X}')

# encrypting the signature should reveal padding + hash
e = 65537
ctext = pow(signature, e, N)

ctext_data = num_to_bytes(ctext, sig_size)
assert ctext_data == padding + list(hash_data)

# OK so the hash is signed, but does the hash match the file?
m = hashlib.sha256()
m.update(info['AvbVBMetaImageHeader']['blob']) # hash header
m.update(info['Auxiliary']['blob']) # hash auxiliary data
print('computed hash = ' + m.hexdigest())
assert m.digest() == hash_data

print('OK')
