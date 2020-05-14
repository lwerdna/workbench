# binja listens on UDP for navigate commands

import socket
import threading

import binaryninja
from binaryninjaui import DockHandler

def worker(bv):
	sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
	sock.bind(('127.0.0.1', 31337))

	while True:
		print('udp_nav: calling sock.recvfrom()')
		data, addr = sock.recvfrom(1024)
		data = data.decode('utf-8')
		address = int(data, 16)
		print("udp_nav: received ", data)

		dh = DockHandler.getActiveDockHandler()
		vf = dh.getViewFrame()
		cv = vf.getCurrentView()
		bv.navigate(cv, address)

def go(bv):
	threading.Thread(target=worker, args=(bv,)).start()

from binaryninja.plugin import PluginCommand
PluginCommand.register("udp nav", "udp nav", go)	
