from helpers import *

from port import Port

class Switch():
    def __init__(self, n_ports):
        self.ports = [Port() for i in range(n_ports)]
        self.table = {}
        self.running = False
        self.igmp_snooping = False

    def run(self):
        self.running = True
        while self.running:
            for i, port in enumerate(self.ports):
                if not port.connected():
                    continue

                frame = port.receive()
                if frame == None:
                    continue

                print(f'SWITCH received frame on port {i}:')
                print(hexdump(frame))
                finfo = parse_ethernet_ii(frame)
                srcmac = finfo['src']
                dstmac = finfo['dst']

                # update mac address table?
                self.update_table(srcmac, i)

                # flood conditions
                flood = False
                if dstmac == mac_bcast:
                    print(f'SWITCH dst mac {mac2str(dstmac)} is broadcast -> flood')
                    flood = True
                if not self.igmp_snooping and mac_is_multicast(dstmac):
                    print(f'SWITCH dst mac {mac2str(dstmac)} is multicast -> flood')
                    flood = True
                if mac_is_unicast(dstmac) and dstmac not in self.table:
                    print(f'SWITCH dst mac {mac2str(dstmac)} is unicast, but not in table -> flood')
                    flood = True

                # send
                if flood:
                    for j, port in enumerate(self.ports):
                        if port.connected() and j != i:
                            print(f'SWITCH sending on port {j}')
                            port.send(frame)
                else:
                    idx = self.table.get(dstmac)
                    port = self.ports[idx]
                    print(f'SWITCH sending on port {idx}')
                    port.send(frame)

    def update_table(self, mac, port_new):
        if mac == mac_bcast:
            print(f'SWITCH src mac {mac2str(mac)} is broadcast, unexpected, ignoring')
            return

        port_current = self.table.get(mac)
        if port_current is None:
            print(f'SWITCH src mac {mac2str(mac)} is NEW, remember port {port_new}')
            self.table[mac] = port_new
        else:
            if port_current != port_new:
                print(f'SWITCH src mac {mac2str(mac)} was port {port_current}, now port {port_new}')
            else:
                # already in table at correct port
                pass

