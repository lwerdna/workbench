#!/usr/bin/python

import usb

YUBICO_VID = 0x1050

def test():
    """
    Get YubiKey USB device.
    
    Optionally allows you to skip n devices, to support multiple attached YubiKeys.
    """
    try:
        # PyUSB >= 1.0, this is a workaround for a problem with libusbx
        # on Windows.
        import usb.core
        import usb.legacy
        devices = [usb.legacy.Device(d) for d in usb.core.find(
            find_all=True, idVendor=YUBICO_VID)]
    except ImportError:
        # Using PyUsb < 1.0.
        import usb
        devices = [d for bus in usb.busses() for d in bus.devices]
    
    for device in devices:
        if device.idVendor == YUBICO_VID:
            print "device.idProduct is: ", device.idProduct
            if device.idProduct in PID.all(otp=True):
                if skip == 0:
                    return device
                skip -= 1
    
    return None

device = test()
print "test() returned: " + str(device)

