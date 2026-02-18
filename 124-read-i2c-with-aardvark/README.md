Try to read the data from a Finisar SFP module using the [Aardvark I2C/SPI Host Adapter](https://www.totalphase.com/products/aardvark-i2cspi/) and the [Osmocom SFP breakout board](https://osmocom.org/projects/misc-hardware/wiki/Sfp-breakout).

Here's [./eeprom_read.py](./eeprom_read.py) reading the EEPROM:

```
00000000: 03 04 00 00 00 00 08 00 00 00 00 01 0c 00 00 00  ................
00000010: 00 00 64 00 46 49 4e 49 53 41 52 20 43 4f 52 50  ..d.FINISAR CORP
00000020: 2e 20 20 20 00 00 90 65 46 43 4c 46 2d 38 35 32  .   ...eFCLF-852
00000030: 31 2d 33 20 20 20 20 20 41 20 20 20 00 00 00 1c  1-3     A   ....
00000040: 00 10 00 00 xx xx xx xx xx xx xx 20 20 20 20 20  ....xxxxxxx     
00000050: 20 20 20 20 31 35 30 34 31 38 20 20 00 00 00 96      150418  ....
00000060: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000070: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000080: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000090: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000a0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000b0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000c0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000d0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000e0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000f0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
Identifier: 3
Ext. Identifier: 4
Connector: 0
BR, Nominal: 12
Vendor name: b'FINISAR CORP.   '
Vendor OUI: b'\x00\x90e'
Vendor PN: b'FCLF-8521-3     '
Vendor rev: b'A   '
Vendor SN: b'xxxxxxx         '
Date code: b'150418  '
```

And [./phy_read.py](./phy_read.py) showing some PHY registers, briding MDIO over the I2C bus exposed by the SFP:

```
Control Register (0): 0x0140
  autoneg disabled
  copper duplex mode
  speed: 1000 Mbps
Status Register (1): 0x016D
  extended status in reg 15
  phy accepts mgmt frames with preamble suppressed
  autoneg process complete
  phy able to perform autoneg
  copper link status (delayed): UP
PHY Specific Status Register (17) - Copper: 0xAC00
  Link (real time): UP
Extended PHY Specific Status Register (27): 0x9088
  Fiber/Copper Auto Selection: enabled
  Fiber/Copper resolution: copper link
  Serial Interface Autoneg bypass: enabled
  Serial Interface Autoneg bypass status: link up due to regular fiber autoneg
  Interrupt Polarity: active high
  automatic medium register selection: enabled
  DTE detect status drop hysteresis: 640 seconds
  DTE power status: does not need DTE power
********
  HWCFG_MODE: 1000BASE-X without Clock with 1000BASE-X Auto-Neg to copper (GBIC)
********
```

See [./setter.py](./setter.py) for how to set some registers.