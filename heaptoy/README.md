Programmatic interface to a compiled heap (dlmalloc).

Example session:

```
$ ./heapshell.py
-------- MemVM id:4449434928 base:0x7F94D2800000 --------
SHELL> malloc 50
allocated 0x32 bytes at 0x7F94D2800010
SHELL> malloc 100
allocated 0x64 bytes at 0x7F94D2800050
SHELL> malloc 200
allocated 0xC8 bytes at 0x7F94D28000C0
SHELL> free 0x7F94D2800050
free'd buffer at 0x7F94D2800050
SHELL> pic
```

Example exported animation (A means alloc, Fx means free the x'th buffer):

![](./assets/animated-heap.gif)