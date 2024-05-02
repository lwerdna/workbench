#!/usr/bin/env python

import os
import sys
import fcntl
import random
import subprocess

from helpers import *


if __name__ == '__main__':

    switch = Switch()
    switch.connect_host(Host('Alice', str2ip('192.168.123.10')))
    hosts.append(Host('Bob', str2ip('192.168.123.11')))
    hosts.append(Host('Charlie', str2ip('192.168.123.12')))

    for host in hosts:
        print(host)

    child = subprocess.Popen('tap2streams', stdout=subprocess.PIPE, stdin=subprocess.PIPE)

    reply_func = lambda f: os.write(child.stdin.fileno(), f)

    while True:
        # wait for child to write to stdout (incoming frame)
        frame = os.read(child.stdout.fileno(), 65536)

        print('ROUTER received frame:')
        print(hexdump(frame))

        finfo = parse_ethernet_ii(frame)
        packet = finfo['payload']

        if finfo['dst'] == b'\xFF\xFF\xFF\xFF\xFF\xFF':
            print('broadcast frame received, sending payload to all hosts!')
            for host in hosts:
                host.receive(finfo['type'], packet, reply_func)
        else:
            print(f'targetted frame received, sending payload to host with mac: {mac2str(finfo["dst"])}')
            for host in hosts:
                if host.mac_addr == finfo['dst']:
                    host.receive(finfo['type'], packet, reply_func)

        # respond with
        #os.write(child.stdin.fileno(), buf)

        
