#!/usr/bin/env python

import os
import select
import subprocess

from port import Port

from helpers import *

class Tap():
    def __init__(self):
        self.running = False
        self.port = Port()

    def run(self):
        self.running = True
        child = subprocess.Popen('tap2streams', stdout=subprocess.PIPE, stdin=subprocess.PIPE)

        while self.running:
            ready, _, _, = select.select([child.stdout], [], [], 0)
            if child.stdout in ready:
                frame = os.read(child.stdout.fileno(), 65536)
                if frame:
                    print('TAP read frame:')
                    print(hexdump(frame))
                    self.port.send(frame)
        
            frame = self.port.receive()
            if frame:
                print('TAP write frame:')
                print(hexdump(frame))
                os.write(child.stdin.fileno(), frame)

        child.stdout.close()
        child.stdin.close()
