from helpers import *

from port import Port

class Switch():
    def __init__(self, n_ports):
        self.ports = [Port() for i in range(n_ports)]
        self.mac_addr_table = {}
        self.running = False

    def run(self):
        self.running = True
        while self.running:
            for i, port in enumerate(self.ports):
                frame = port.receive()
                if frame == None:
                    continue

                print(f'SWITCH received frame on port {i}:')
                print(hexdump(frame))
                finfo = parse_ethernet_ii(frame)
                srcmac = finfo['src']
                dstmac = finfo['dst']

                # update mac address table?
                if not srcmac in self.mac_addr_table:
                    print(f'SWITCH adding {mac2str(srcmac)} -> port {i} mapping')
                    self.mac_addr_table[srcmac] = i

                if dstmac == b'\xFF\xFF\xFF\xFF\xFF\xFF':
                    outidxs = [j for j in range(len(self.ports)) if j != i]
                    print(f'SWITCH broadcast, repeating on ports {outidxs}')
                    for idx in outidxs:
                        self.ports[idx].send(frame)
                    continue

                print(f'SWITCH unicast, searching for: {mac2str(dstmac)}')
                pi = self.mac_addr_table.get(dstmac)
                if pi == None:
                    print(f'SWITCH not found, discarding frame')
                    continue

                print(f'SWITCH sending to port {pi}')
                self.ports[pi].send(frame)
