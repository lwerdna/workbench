#!/usr/bin/python

# "unlock" your yubikey sky from linux's hid driver

import usb

YUBICO_VENDOR_ID = 0x1050
NEO_SKY_PROD_ID = 0x120

dev = usb.core.find(idVendor=YUBICO_VENDOR_ID, idProduct=NEO_SKY_PROD_ID)
if dev is None: raise ValueError('Device not found')
dev.detach_kernel_driver(0) 

