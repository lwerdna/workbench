Use an Arduino ESP32 to read/write MDIO on a TI PHY dev board.

See tool/tool.ino for the Arduino sketch, which you can open in Arduino IDE or use the Makefile to compile on the command line.s

Only three wires to the PHY!

```

+------------------+   serial    +---------+   bit banging   +--------+
| python scripts   | <---------> | ARDUINO | <-------------> | TI PHY |
| w/ serial module |             +---------+      MDIO       +--------+
+------------------+
```

