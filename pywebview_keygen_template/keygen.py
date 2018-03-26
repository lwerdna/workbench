#!/usr/bin/env python

import os
import sys
import time
import random
import hashlib
import webview
import binascii
import threading

# javascript calling this back
class Api:
	def __init__(self):
		pass

	def generate(self, params):
		m = hashlib.md5()
		m.update(params)
		result = binascii.hexlify(m.digest())
		result = '%s-%s-%s-%s' % (result[0:8], result[8:16], result[16:24], result[24:32])
		return {'message': result}

def logic_thread():
	# get path to local files
	fpath = os.path.abspath(__file__)
	fpath = os.path.join(os.path.split(fpath)[0], "gui.html")

	# wait until window ready
	while True:
		print 'checking if window ready...'
		if webview.window_exists():
			break
		time.sleep(.1)

	# load gui html file
	print "get_current_url() returns: ", webview.get_current_url()
	webview.load_url(fpath)
	print "get_current_url() returns: ", webview.get_current_url()

if __name__ == '__main__':
	t = threading.Thread(target=logic_thread)
	t.start()

	print 'calling create_window()'
	api = Api()
	webview.create_window('API example', js_api=api, debug=True)



