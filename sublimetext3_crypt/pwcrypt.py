import sublime, sublime_plugin

import re
import base64
import struct
import hashlib
import binascii
import threading

from alib.crypto.xtea import xtea_encrypt_ofb

gKey = None

class CachePassphraseCommand(sublime_plugin.WindowCommand):
	def run(self):
		self.window.show_input_panel("Passphrase:", "", self.getKeyCallback, None, None)

	def getKeyCallback(self, passPhrase):
		global gKey

		print("passphrase as ST string, before utf-8 encoding: " + passPhrase)
		passPhrase = passPhrase.encode('utf-8')
		print("passphrase bytes, after encoding: " + str(binascii.hexlify(passPhrase)))
		m = hashlib.sha1(passPhrase)
		digest = m.digest()
		gKey = digest[0:16]
		print("key: " + str(binascii.hexlify(gKey)))

class ClearPassphraseCommand(sublime_plugin.WindowCommand):
	def run(self):
		gKey = None

class EncryptCommand(sublime_plugin.TextCommand):
	def run(self, edit):
		if not gKey:
			sublime.error_message("no key, cache your passphrase")
			return

		regions = self.view.sel()

		for region in regions:
			ptextStr = self.view.substr(region)
			ptextBin = ptextStr.encode('utf-8')
			ctextBin = xtea_encrypt_ofb(ptextBin, gKey)
			ctextB64Bin = binascii.b2a_base64(ctextBin)
			ctextB64Str = ctextB64Bin.decode('utf-8')
			# b2a_base64() adds newline character, rid it
			ctextB64Str = ctextB64Str.strip()
			self.view.replace(edit, region, ctextB64Str)

class DecryptCommand(sublime_plugin.TextCommand):
	def run(self, edit):
		global gKey

		if not gKey:
			sublime.error_message("no key, cache your passphrase")
			return

		regions = self.view.sel()

		for region in regions:
			ctextB64Str = self.view.substr(region)
			ctextBin = binascii.a2b_base64(ctextB64Str)
			ptextBin = xtea_encrypt_ofb(ctextBin, gKey)
			ptextStr = ptextBin.decode('utf-8')
			print("The plaintext string is -" + ptextStr + "-")
			#ptextStr = ptextStr.strip()
			self.view.replace(edit, region, ptextStr)
