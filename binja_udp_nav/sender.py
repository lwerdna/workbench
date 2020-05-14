#!/usr/bin/env python

import socket

UDP_IP = "127.0.0.1"
UDP_PORT = 31337

#print "UDP target IP:", UDP_IP
#print "UDP target port:", UDP_PORT
#print "message:", MESSAGE

sock = socket.socket(socket.AF_INET, # Internet
                     socket.SOCK_DGRAM) # UDP

while 1:
	print('message: ', end='')
	message = input()
	message = message.strip()
	message = message.encode('utf-8')
	sock.sendto(message, (UDP_IP, UDP_PORT))
