#!/usr/bin/env python

import os
import sys
import time
import random
import signal
import subprocess
import threading

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
    nic0 = NIC()
    connect(host0.nic, nic0.host)

    host1 = Host('Bob', str2ip('192.168.123.11'))
    nic1 = NIC()
    connect(host1.nic, nic1.host)

    host2 = Host('Charlie', str2ip('192.168.123.12'))
    nic2 = NIC()
    connect(host2.nic, nic2.host)

    switch = Switch(8)
    connect(switch.ports[0], nic0.rj45)
    connect(switch.ports[1], nic1.rj45)
    connect(switch.ports[2], nic2.rj45)

    tapPort = Port()
    connect(tapPort, switch.ports[7])
    
    # turn everything on
    threads = []
    devices = [host0, host1, host2, nic0, nic1, nic2, switch]
    for device in devices:
        t = threading.Thread(target=device.run, args=tuple())
        threads.append(t)
        t.start()

    running = True
    ping_sent = False
    while running:
        # get packets from
        if not ping_sent:
            print('send packet to switch')
            ping_192_168_10_99 = b''
            ping_192_168_10_99 += b'\xFF\xFF\xFF\xFF\xFF\xFF\x96\x75\x6B\x18\xEC\xC5\x08\x06\x00\x01'
            ping_192_168_10_99 += b'\x08\x00\x06\x04\x00\x01\x96\x75\x6B\x18\xEC\xC5\xC0\xA8\x0A\x63'
            ping_192_168_10_99 += b'\x00\x00\x00\x00\x00\x00\xC0\xA8\x0A\x01'
            tapPort.send(ping_192_168_10_99)
            ping_sent = True

    print('simulation ending')
    for i in range(len(threads)):
        print(f'shutting down device {i}')
        devices[i].running = False
        threads[i].join()

    print('DONE')

    #child = subprocess.Popen('tap2streams', stdout=subprocess.PIPE, stdin=subprocess.PIPE)

#    while True:
#        # wait for child to write to stdout (incoming frame)
#        frame = os.read(child.stdout.fileno(), 65536)
#
#        print('ROUTER received frame:')
#        print(hexdump(frame))
#
#        finfo = parse_ethernet_ii(frame)
#        packet = finfo['payload']
#
#        if finfo['dst'] == b'\xFF\xFF\xFF\xFF\xFF\xFF':
#            print('broadcast frame received, sending payload to all hosts!')
#            for host in hosts:
#                host.receive(finfo['type'], packet, reply_func)
#        else:
#            print(f'targetted frame received, sending payload to host with mac: {mac2str(finfo["dst"])}')
#            for host in hosts:
#                if host.mac_addr == finfo['dst']:
#                    host.receive(finfo['type'], packet, reply_func)
#
        # respond with
        #os.write(child.stdin.fileno(), buf)

    

