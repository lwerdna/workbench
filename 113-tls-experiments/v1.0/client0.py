#!/usr/bin/env python

# USING TLSLITE-NG
# pip install tlslite-ng

import sys
import socket

from tlslite import TLSConnection
from tlslite.api import *

ip, port = sys.argv[1:]

sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
sock.connect((ip, int(port)))

connection = TLSConnection(sock)

settings = HandshakeSettings()
settings.maxVersion = (3,1) # (3,0) is SSL 3.0, (3,1) is TLS 1.0
settings.minVersion = (3,1)
# client is anonymous, client requires server have cert
connection.handshakeClientCert(settings=settings)

print(f'client random: {connection._clientRandom.hex()}')
print(f'server random: {connection._serverRandom.hex()}')

sess = connection.session
print(sess)

print(f'master secret: {sess.masterSecret.hex()}')
print(f'   session id: {sess.sessionID.hex()}')
print(f'       cipher: {sess.getCipherName()}')
print(f'          mac: {sess.getMacName()}')

if 1:
    fpath = '/tmp/test.keylogfile'
    print(f'writing: {fpath}')
    with open(fpath, 'w') as fp:
        fp.write(f'CLIENT_RANDOM {connection._clientRandom.hex()} {sess.masterSecret.hex()}\n')

# write(), send(), sendall()
connection.sendall("Hello, world!\n".encode('utf-8'))
connection.sendall(b'\x41\x42\x43\x44') # "ABCD"

print(connection.read())
