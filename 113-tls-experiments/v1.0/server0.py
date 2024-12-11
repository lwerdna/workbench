#!/usr/bin/env python

import sys
import ssl
import socket

from tlslite import TLSConnection
from tlslite.api import *

x509 = X509()
x509.parse(open('server_cert.pem').read())
certChain = X509CertChain([x509])

privateKey = parsePEMKey(open('server_key.pem').read(), private=True)

host = 'localhost' #socket.gethostname()
port = 31337
sock = socket.socket()
print(f'binding to {host}:{port}')
sock.bind((host, int(port)))
print(f'listen(1)')
sock.listen(1)
print(f'accept()')
conn, addr = sock.accept()
print(f'connection from: {addr}')

connection = TLSConnection(conn)

# do handshake
settings = HandshakeSettings()
settings.maxVersion = (3,1)
settings.minVersion = (3,1)
connection.handshakeServer(certChain=certChain, privateKey=privateKey, settings=settings, anon=True)

# receive something
while True:
    data = connection.recv(1024).decode()
    print(data, end='')

conn.close()
sock.close()
