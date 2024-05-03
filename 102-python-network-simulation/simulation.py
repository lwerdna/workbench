#!/usr/bin/env python

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
    host0 = Host('Alice', str2ip('192.168.123.10'))
    host1 = Host('Bob', str2ip('192.168.123.11'))
    host2 = Host('Charlie', str2ip('192.168.123.12'))

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
