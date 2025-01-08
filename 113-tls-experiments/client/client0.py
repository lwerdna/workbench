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
settings.maxVersion = (3,3) # (3,0) is SSL 3.0, (3,1) is TLS 1.0
settings.minVersion = (3,3)
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

def recv_until(connection, what='\n'):
    buf = b''
    while not buf.endswith(b'\x0a'):
        buf += connection.recv(1)
    return buf

# write(), send(), sendall()
connection.sendall('Hello, world!\n'.encode('utf-8'))
print('GOT:', recv_until(connection))
connection.sendall('How are you?\n'.encode('utf-8'))
print('GOT:', recv_until(connection))
connection.sendall('I am leaving now.\n'.encode('utf-8'))
print('GOT:', recv_until(connection))
connection.sendall('Bye!\n'.encode('utf-8'))
connection.close()
sock.close()
