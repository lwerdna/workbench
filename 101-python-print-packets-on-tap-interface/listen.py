#!/usr/bin/env python

# create a tap2stdout child process and emit frame as hex dump

import os
import subprocess

# https://gist.github.com/mzpqnxow/a368c6cd9fae97b87ef25f475112c84c
def hexdump(src, addr=0, length=16, sep='.'):
    FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or sep for x in range(256)])
    lines = []
    for c in range(0, len(src), length):
        chars = src[c: c + length]
        hex_ = ' '.join(['{:02x}'.format(x) for x in chars])
        if len(hex_) > 24:
            hex_ = '{}{}'.format(hex_[:24], hex_[24:])
        printable = ''.join(['{}'.format((x <= 127 and FILTER[x]) or sep) for x in chars])
        lines.append('{0:08x}: {1:{2}s} {3:{4}s}'.format(addr+c, hex_, length * 3, printable, length))
    return '\n'.join(lines)

if __name__ == '__main__':
    child = subprocess.Popen('tap2stdout', stdout=subprocess.PIPE)

    # this is from a stackoverflow answer, but is not necessary
    #import fcntl
    #fd = child.stdout.fileno()
    #fl = fcntl.fcntl(fd, fcntl.F_GETFL)
    #fcntl.fcntl(fd, fcntl.F_SETFL, fl | os.O_NONBLOCK)

    while True:
        # wait for child to write to stdout (incoming frame)
        frame = os.read(child.stdout.fileno(), 65536)
        print(hexdump(frame))
        print()
