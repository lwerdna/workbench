Demonstrate communication from BinaryNinja plugins written in Python to plugins written in C/C++.

**TLDR**: [ctypes](https://docs.python.org/3/library/ctypes.html) on the path to a plugin will return a handle to the already loaded object in BinaryNinja's process. See [./testcomms.py](./testcomms.py) for the python plugin and [./test.cpp](./test.cpp) for the C/C++ plugin.

Build it with `make` and `make install`, pointing those environment variables in the Makefile appropriately.

Run BinaryNinja and in the python console enter:

```
>>> import testcomms
>>> testcomms.say(5, "five")
loading: /Users/username/Library/Application Support/Binary Ninja/plugins/test.dylib
handle: <CDLL '/Users/username/Library/Application Support/Binary Ninja/plugins/test.dylib', handle 7fc658b04f90 at 0x14090b7d0>
(PYTHON) received 234
```

In the BinaryNinja log window you should see:

```
c++/LogInfo(): foo=5 bar=five
```

This demonstrates sending an integer, string, and receiving a return value.

## Story

I could think of no good way, and was suggested the typical [IPC](https://en.wikipedia.org/wiki/Inter-process_communication) ideas like sockets, pipes, and shared memory and more exotic routes like [zeromq](https://zeromq.org/) and setting/detecting changes in a binaryview's meta data.

Then my coworker **Glenn** has the simplest and most elegant idea: [ctypes](https://docs.python.org/3/library/ctypes.html).

What? I need a handle to the C/C++'s plugin's shared object in BinaryNinja's memory, not to some arbitrary path on disk. But ctypes's underlying mechanism (guesses: `LoadLibrary()` or `dlopen()`) will give you the existing handle if already loaded, not load it again!





