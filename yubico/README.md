These are some tools to play with the Yubico U2F-only ("NEO Sky") USB dongle sold for $5 thru the github promotional in October 2015.

* a shell to interact with the dongle, using python and pyusb
* (PLANNED) a shell to interact with the dongle, using FIDO U2F javascript API
* (PLANNED) a "spy" that reports on the dongle's activity as your browser 

[screenshot](./media/screenshot0.png?raw=true "screenshot")

###communication stack
    +------------------+
    | U2F              | TRANSACTIONS
    |                  | (encapsulated in U2FHID_MSG)
    |                  |
    +------------------+ 
    | U2FHID           | MESSAGES
    |                  | - logical channels: 0 (reserved), ..., 0xFFFFFFFF (broadcast)
    |                  | - commands: U2FHID_INIT, U2FHID_PING, U2FHID_WINK
    |                  | - initialization and continuation packets
    +------------------+
    | USB REPORT       | PACKETS
    |                  | - IN and OUT endpoints
    |                  | - 64-byte chunks (HID_RPT_SIZE)
    +------------------+
    | LINUX USB SUBSYS |
    +------------------+
    | USB BUS          |
    +------------------+
    | DONGLE           |
    +------------------+

###device structure
* one HID device, one config, one interface, two endpoints, lsbusb gives:
    device descr (Bus 002 Device 012: ID 1050:0120 Yubico.com)
      config descr
        interface descr (class: HID)
          endpoint descr (addr: 0x04 EP 4 OUT) (pkt size: 64)
          endpoint descr (addr: 0x84 EP 4 IN)  (pkt size: 64)

###debuggin USB presence issues
* simple `dmesg` to watch insertion, example output:
    [771880.315804] usb 2-2.2: new full-speed USB device number 9 using uhci_hcd
    [771880.531468] usb 2-2.2: New USB device found, idVendor=1050, idProduct=0120
    [771880.531473] usb 2-2.2: New USB device strings: Mfr=1, Product=2, SerialNumber=0
    [771880.531475] usb 2-2.2: Product: Security Key by Yubico
    [771880.531477] usb 2-2.2: Manufacturer: Yubico
    [771880.550951] hid-generic 0003:1050:0120.0002: hiddev0,hidraw1: USB HID v1.10 Device [Yubico Security Key by Yubico] on usb-0000:02:00.0-2.2/input0
* `lsusb` to find your device
* `lsusb -v -d 1050:0120` for details

###debugging protocol issues
* find fido-u2f-u2f.h and fido-u2f-u2fhid.h
* https://fidoalliance.org/specifications/download/

###debugging pylib issues
* find docs with `pydoc usb` or within python `help(usb)`
* code (in my case) is in /usr/local/lib/python2.7/dist-packages/pyusb-1.0.0b2-py2.7.egg (treat like zip file)

###pitfalls
* don't use yubico-python; though it has knowledge of product id 0x120 (NEO_SKY), it won't detect, and if you patch it to detect, it will hang waiting for some status bits to clear during a protocol step
* don't use the yubikey personalizatoin tool in OSX, it simply won't detect the thing
* don't use the yubikey personalization tool in Linux, 'cause it's impossible to compile!
* don't use the command-line personalization tool in Linux (ykpers), it won't detect
* DON'T THINK THIS IS ANYTHING LIKE A TYPICAL YUBICO PRODUCT, IT'S U2F ONLY

