Generically decompress a zImage by emulating it in unicorn.

* [method0.py](./method0.py) - uses memory tracking
* method1.py - provides sentinel address for ATAGS to trap ARM kernel execution (TODO)

Other files:

* [emulate_uImage.py](./emulate_uImage.py) - tool to help trace and debug kernels as they decompress, uses project 000

See [DEVNOTES.txt](./DEVNOTES.txt) for stream of consciousness.
