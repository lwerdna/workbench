# binja listens on UDP for navigate commands

import socket
import threading

import binaryninja
headless = False
try:
	from binaryninjaui import DockHandler
except ModuleNotFoundError:
	headless = True

def worker(bv):
	sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
	sock.bind(('127.0.0.1', 31337))

	while True:
		print('udp_nav: calling sock.recvfrom()')
		data, addr = sock.recvfrom(1024)
		print("udp_nav: received ", data)

		try:
			data = data.decode('utf-8')
			address = int(data, 16)
		except Exception:
			continue

		dh = DockHandler.getActiveDockHandler()
		vf = dh.getViewFrame()
		cv = vf.getCurrentView()
		print('udp_nav: bv.navigate(\'%s\', 0x%X)' % (cv, address))
		bv.navigate(cv, address)

def go(bv):
	threading.Thread(target=worker, args=(bv,)).start()

if not headless:
	from binaryninja.plugin import PluginCommand
	PluginCommand.register("udp nav", "udp nav", go)	
