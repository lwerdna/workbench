## notes

PI in hex is:

```
3.243F6A8885A308D313198A2E037073..
```

Why does `math.pi.hex()` yield "0x1.921f9f01b866ep+1"?

The `.` is now "hexadecimal point" (vs. decimal point) and the "ep+1" means to adjust by `2**1`. Agreement is confirmed with `hex(0x1921f9f01b8866*2)` yielding `0x3243f3e03710cc`.

