from helpers import *

from port import Port

class Host:
    def __init__(self, label, ip_addr):
        self.label = label
        self.ip_addr = ip_addr
        self.arp_table = {} # ip -> mac
        self.nic = Port() # port to nic
        self.running = False

    def run(self):
        self.running = True
        while self.running:
            frame = self.nic.receive()
            if frame == None:
                continue

            print(f'{self} received frame')
            print(hexdump(frame))

            finfo = parse_ethernet_ii(frame)
            match finfo['type']:
                # IPv4
                case 0x0800:
                    self.handle_ipv4(finfo['payload'])
                # ARP
                case 0x0806:
                    self.handle_arp(finfo['payload'])
                case _:
                    print(f'unknown type: 0x{finfo["type"]:X}')

    def handle_ipv4(packet):
        ipv4_info = parse_ipv4(packet)
        if ipv4_info['dst_addr'] != self.ip_addr:
            return
        if ipv4_info['protocol'] == 1: # is ICMP?
            icmp_packet = ipv4_info['payload']
            icmp_info = parse_icmp(icmp_packet)
            match icmp_info['type']:
                case 8: # echo request (ping)
                    reply = b''
                    # add layer 2 (ethernet)
                    ethhdr = self.arp_table[ipv4_info['src_addr']] # eth destination
                    ethhdr += self.mac_addr # eth source
                    ethhdr += b'\x08\x00' # eth type: IPv4
                    reply += ethhdr
                    assert len(reply) == 14
                    # add layer 3 (IP)
                    iphdr = b'\x45' # version, len
                    iphdr += b'\x00' # differentiated services
                    iphdr += struct.pack('!H', 20 + len(icmp_packet)) # total length
                    iphdr += struct.pack('!H', ipv4_info['ident']+1) # identification
                    iphdr += b'\x00\x00' # flags: don't frag
                    iphdr += b'\x40' # ttl: 64
                    iphdr += b'\x01' # protocol: ICMP
                    iphdr += b'\x00\x00' # header checksum
                    iphdr += self.ip_addr # source address
                    iphdr += ipv4_info['src_addr'] # dest address
                    iphdr = iphdr[0:10] + calc_checksum_h(iphdr) + iphdr[12:]
                    reply += iphdr
                    assert len(reply) == 14 + 20
                    # add layer 3 (ICMP)
                    icmp = b'\x00' # type: echo reply
                    icmp += icmp_packet[1:2] # code
                    icmp += b'\x00\x00' # checksum
                    icmp += icmp_packet[4:6] # identifier
                    icmp += icmp_packet[6:8] # sequence number
                    icmp += icmp_packet[8:16] # timestamp
                    icmp += icmp_packet[16:] # data
                    icmp = icmp[0:2] + calc_checksum_h(icmp) + icmp[4:]
                    reply += icmp
                    assert len(reply) == 14 + 20 + len(icmp_packet)

                    self.nic.send(reply)
                case _:
                    return

    def handle_arp(self, packet):
        ainfo = parse_arp(packet)
        
        print(f'sender mac:{mac2str(ainfo["sender_mac"])} ip:{ip2str(ainfo["sender_ip"])}')
        print(f'target mac:{mac2str(ainfo["target_mac"])} ip:{ip2str(ainfo["target_ip"])}')

        self.arp_table[ainfo['sender_ip']] = ainfo['sender_mac']

        match ainfo['opcode']:
            case 1: # request
                if not (ainfo['target_mac'] in [b'\x00'*6, self.mac_addr]): # matches our mac or is wildcard
                    return
                if not ainfo['target_ip'] == self.ip_addr:
                    return
                reply = b''
                # add layer 2 (ethernet)
                reply += ainfo['sender_mac'] # eth destination
                reply += self.mac_addr # eth source
                reply += b'\x08\x06' # eth type: ARP
                # add layer 2 (ARP)
                reply += b'\x00\x01' # hw type
                reply += b'\x08\x00' # protocol type
                reply += b'\x06' # hw size
                reply += b'\x04' # protocol size
                reply += b'\x00\x02' # opcode: reply
                reply += self.mac_addr # sender mac
                reply += self.ip_addr # sender ip
                reply += ainfo['sender_mac'] # target mac
                reply += ainfo['sender_ip'] # target ip
                print(f'{self} replying!')
                reply_func(reply)

            case 2: # reply
                pass
            case _:
                pass

    def __str__(self):
        return f'HOST "{self.label}" ip={ip2str(self.ip_addr)}'
