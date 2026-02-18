Use an Arduino ESP32 to read/write MDIO on a TI PHY dev board.

See tool.ino for the Arduino sketch.

Only three wires to the PHY!

```

+------------------+   serial    +---------+   bit banging   +--------+
| python scripts   | <---------> | ARDUINO | <-------------> | TI PHY |
| w/ serial module |             +---------+      MDIO       +--------+
+------------------+
```

