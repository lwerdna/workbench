from helpers import *

from port import Port

class NIC():
    def __init__(self, macaddr=None):
        if not macaddr:
            macaddr = generate_mac()
        self.macaddr = macaddr
        self.rj45 = Port()
        self.host = Port()
        self.promiscuous = False
        self.running = False

    def run(self):
        self.running = True
        while self.running:
            frame = self.rj45.receive()
            if frame != None:
                print(f'NIC received frame on rj45 port')
                print(hexdump(frame))

                finfo = parse_ethernet_ii(frame)
                if finfo['dst'] == self.macaddr or finfo['dst'] == mac_bcast:
                    self.host.send(frame)

            frame = self.host.receive()
            if frame != None:
                print(f'NIC received frame from host')
                print(hexdump(frame))
                self.rj45.send(Frame)
