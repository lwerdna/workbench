from helpers import *

from port import Port

class NIC():
    def __init__(self, macaddr=None):
        if not macaddr:
            macaddr = generate_mac()
        self.macaddr = macaddr

        self.rj45 = Port() # the side representing where cat5 would connect
        self.bus = Port() # the side representing where the host would connect

        self.promiscuous = False

        self.running = False

    def run(self):
        self.running = True
        while self.running:
            # rj45 -> host
            frame = self.rj45.receive()
            if frame != None:
                #print(f'NIC received frame on rj45 port')
                #print(hexdump(frame))

                finfo = parse_ethernet_ii(frame)
                if finfo['dst'] in [self.macaddr, mac_bcast, mac_loopback]:
                    self.bus.send(frame)

            # host -> rj45
            frame = self.bus.receive()
            if frame != None:
                #print(f'NIC received frame from host')
                #print(hexdump(frame))
                self.rj45.send(frame)
