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

reqCert = False
anon = False
for arg in sys.argv:
    if 'reqcert' in arg.lower():
        reqCert = True
    if 'anon' in arg.lower():
        anon = True

host = '0.0.0.0' #socket.gethostname()
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
settings.maxVersion = (3,3)
settings.minVersion = (3,3)

print(f'{sys.argv[0]} anon    # anonymous client, server auths with cert')
print(f'{sys.argv[0]} reqCert # client and server auths with cert')

# reqCert   anon  effect
# ------- ------  ------
#   false   true  anonymous client, server authenticates with self-signed cert
#    true   false client and server authenticates with self-signed cert
connection.handshakeServer(certChain=certChain, privateKey=privateKey, settings=settings, reqCert=reqCert, anon=anon)

# receive something
while True:
    data = connection.recv(1024).decode()
    print(data, end='')

conn.close()
sock.close()
