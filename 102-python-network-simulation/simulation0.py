#!/usr/bin/env python

# +----------------+
# | SWITCH  port 0 |---- virtual host "Alice"   192.168.123.10 AA:AA:AA:AA:AA:AA
# |         port 1 |---- virtual host "Bob"     192.168.123.11 BA:BB:BB:BB:BB:BB
# |         port 2 |---- virtual host "Charlie" 192.168.123.12 CC:CC:CC:CC:CC:CC
# |         port 3 |
# |         port 4 |
# |         port 5 |
# |         port 6 |
# |         port 7 |---- tap (Host linux)       192.168.123.1
# +----------------+

import time
import signal
import threading

from tap import Tap
from nic import NIC
from host import Host
from port import Port
from switch import Switch

from helpers import *

running = False

def signal_handler(sig, frame):
    global running
    running = False

if __name__ == '__main__':
    signal.signal(signal.SIGINT, signal_handler)

    # set up network
    host0 = Host('Alice', str2ip('192.168.123.10'), b'\xAA\xAA\xAA\xAA\xAA\xAA')
    host1 = Host('Bob', str2ip('192.168.123.11'), b'\xBA\xBB\xBB\xBB\xBB\xBB')
    host2 = Host('Charlie', str2ip('192.168.123.12'), b'\xCC\xCC\xCC\xCC\xCC\xCC')

    switch = Switch(8)
    connect(switch.ports[0], host0.nic.rj45)
    connect(switch.ports[1], host1.nic.rj45)
    connect(switch.ports[2], host2.nic.rj45)

    tap = Tap()
    connect(tap.port, switch.ports[7])
    
    # turn everything on
    threads = []
    devices = [host0, host1, host2, host0.nic, host1.nic, host2.nic, switch, tap]
    for device in devices:
        t = threading.Thread(target=device.run, args=tuple())
        threads.append(t)
        t.start()

    running = True
    while running:
        time.sleep(1)

    print('simulation ending')
    for i in range(len(threads)):
        print(f'shutting down device {i}')
        devices[i].running = False
        threads[i].join()
