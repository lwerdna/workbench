What's the fastest way to use capstone disassembler?

* a binary (c++ linked against libcapstone) - see binary.cpp
* python using the python bindings - see bindings.py
* python manually calling a small thunk shared object thru ctypes - see binthunk.py and binthunk.cpp

This experiment goes through the first 64k instructions, and here are the results:

| experiment   | time                                                        |
| ------------ | ----------------------------------------------------------- |
| binary       | real	0m0.852s<br />user	0m0.843s<br />sys	0m0.006s |
| bindings     | real	0m11.771s<br />user 0m11.263s<br />sys 0m0.343s     |
| binary thunk | real	0m3.053s<br />user 0m2.994s<br />sys 0m0.040s       |

All timings done with `$ time ./binthunk.py 1>/dev/null`. Obviously a lot of factors go into how long it takes a program to run, but a safe conclusion I'm willing to draw is that binaries are 1100% faster than python bindings, and manually using ctypes with a little helper program is about 400% faster than python bindings.