#!/usr/bin/python

# thanks to:
# - arducam osd GUI code by Michael Oborne
# - avrdude code by Lars Immisch
# - open bootloader code ATmegaBOOT_168.c

import serial
import time
import binascii

ser = serial.Serial('/dev/ttyUSB0', 57600, timeout=1, dsrdtr=True)

#print dir(ser)
#print ser

for i in range(50):
    if not ser.isOpen():
        print "ERROR: not even open anymore"
        break

    print "attempting reset"
    ser.setDTR(False)
    time.sleep(.050)
    ser.setDTR(True)

    print "attemting read"
    ser.read(9999)
    ser.write('1 ')
    resp = ser.read(9999);
    #print "got back: %s" % (binascii.hexlify(resp))
    print "got back: %s" % repr(resp)

    
