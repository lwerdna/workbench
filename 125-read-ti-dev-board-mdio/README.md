Use an Arduino ESP32 to read/write MDIO on a TI PHY dev board.

See dongle/dongle.ino for the Arduino sketch, which you can open in Arduino IDE or use the Makefile to compile on the command line.

Only three wires to the PHY (MDIO, MDC, GND).

```

+------------------+   serial    +---------+   bit banging   +--------+
| python scripts   | <---------> | ARDUINO | <-------------> | TI PHY |
| w/ serial module |             |  DONGLE |      MDIO       +--------+
+------------------+             +---------+
```

