console only minimOSD

# setup
The ATmega328P does not communicate with you over the FTDI cable by default. When it executes the bootloader, the bootloader's logic initializes the UARTs and talks to you, implementing an in-service programmer (ISP.

## install bootloader
The default bootloader of the ATmega328P initializes the UARTS and communicates to you over your serial cable. It implements an in-service programmer so that subsequent programming no longer requires the USBasp.

### install programmer
* after insertion, dmesg should give:
```
[217216.111060] usb 2-2.2: New USB device found, idVendor=16c0, idProduct=05dc
[217216.111063] usb 2-2.2: New USB device strings: Mfr=1, Product=2, SerialNumber=0
```
* `lsusb` should give:
```
Bus 002 Device 011: ID 16c0:05dc Van Ooijen Technische Informatica shared ID for use with libusb
```
* verify that `avrdude -c usbasp -p m328p` gives back device signature 0x1e950f

### obtain, write bootloader
* comes with debian package "arduino"
* source /usr/share/arduino/hardware/arduino/bootloaders/atmega/ATmegaBOOT_168.c
* write with `avrdude -c usbasp -p m328p -U flash:w:/usr/share/arduino/hardware/arduino/bootloaders/ATmegaBOOT_168_atmega328.hex`

## com
* probably using an FTDI cable or knockoff with FT232R controller - implementing 


* EEPROM locked? try (thanks sbeni...@gmail.com)
```
avrdude -c usbasp -p m328p -U lfuse:w:0xFF:m  
avrdude -c usbasp -p m328p -U hfuse:w:0xDA:m
avrdude -c usbasp -p m328p -U efuse:w:0x05:m
```

originally started: 2015-12-08
