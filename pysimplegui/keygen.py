#!/usr/bin/env python

import binascii
import hashlib
import PySimpleGUI as sg

def computeKey(user):
	m = hashlib.md5()
	m.update(user.encode('utf-8'))
	out = m.digest()
	return binascii.hexlify(out).decode('utf-8')

userInit = 'The quick brown fox jumps over the lazy dog.'

if __name__ == '__main__':
	layout = [
		[sg.Text('User:'), sg.InputText(userInit, change_submits=True, do_not_clear=True, key='_USER_')],
		[sg.Text('Key:'), sg.InputText(computeKey(userInit), disabled=True, key='_KEY_')],
		[sg.Button('Generate')],
	]

	window = sg.Window('Keygen', auto_size_text=True).Layout(layout)

	while (True):
		event, values = window.Read()

		if event == None:
			break
		elif event == '__TIMEOUT__':
			pass
		elif event == '_USER_':
			user = values['_USER_']
			key = computeKey(user)
			window.FindElement('_KEY_').Update(value=key)
		elif event == 'Generate':
			sg.Popup('You clicked the button!')
		else:
			print('unknown event: ', event)

	window.Close()
