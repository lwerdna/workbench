Try to read the data from an SPI chip using the [Aardvark I2C/SPI Host Adapter](https://www.totalphase.com/products/aardvark-i2cspi/).

Here's [get_id.py](./get_id.py) attempting to read the JEDEC ID (command 0x9F) with a saleae Logic Pro 8 analyzer attached. You can clearly see the 0x9f, then 0x00, 0x00, 0x00 to clock in the response. MISO is quiet here since no chip is attached, just the logic analyzer:

![](./assets/aardvark_read_jedec.png)

## Unsorted Notes

```user manual:
https://www.totalphase.com/support/articles/200397858-level-shifter-board-user-manual/
https://www.totalphase.com/support/articles/200349236-spi-background

from the jumper settings we know all possible logic levels:
  1.2V, 1.5V, 1.8V, 2.5V, 3.0V, 3.3V

pins:
  TPWR on 'EXT TGT' group - target power
    supply this pin if target is powering the target side of the board
    view this pin if Aardvark is powering the target side of the board (TPWR connected by jumper)
  SCK serial clock
  SS slave select (active low: is usuall high but goes low upon selection)

Parameters with standard values according to saleae Logic2
  endian: MSB
  bits per transfer: 8
  clock state: CPOL=0 (low when inactive)
  clock phase: CPHA=0 (data valid on leading edge)
  enable line: active low (go low to activate)
```