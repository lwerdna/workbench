#!/usr/bin/env python

import glob
import time
import pprint
import serial # pip install pyserial

import helpers

modems = []

for fpath in glob.glob('/dev/ttyUSB*'):
    response = helpers.open_modem_send_command(fpath, 'AT\r')
    if response == 'OK':
        modems.append(fpath)

        response = helpers.open_modem_send_command(fpath, 'ATI\r')
        print(response)

pprint.pprint(modems)
