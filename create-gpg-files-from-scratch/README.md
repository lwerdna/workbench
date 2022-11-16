Demonstrate creating GnuPG files from first principles.

* [version0.py](./version0.py) - old, minimal implementation in python2 using three packets
* [version1.py](./version1.py) - updated to python3
* [version2.py](./version2.py) - add ascii armor

### TODO

- support ciphers beyond CAST5
- use integrity-protected packet (tag:18) instead of not integrity protected version (tag:9)
