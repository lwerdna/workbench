# helper functions for python scripts

import re
import struct
import random

mac_bcast = b'\xFF\xFF\xFF\xFF\xFF\xFF'

# https://gist.github.com/mzpqnxow/a368c6cd9fae97b87ef25f475112c84c
def hexdump(src, addr=0, length=16, sep='.'):
    FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or sep for x in range(256)])
    lines = []
    for c in range(0, len(src), length):
        chars = src[c: c + length]
        hex_ = ' '.join(['{:02x}'.format(x) for x in chars])
        if len(hex_) > 24:
            hex_ = '{}{}'.format(hex_[:24], hex_[24:])
        printable = ''.join(['{}'.format((x <= 127 and FILTER[x]) or sep) for x in chars])
        lines.append('{0:08x}: {1:{2}s} {3:{4}s}'.format(addr+c, hex_, length * 3, printable, length))
    return '\n'.join(lines)

def parse_ethernet_ii(frame):
    # preamble and crc are stripped by lower layers
    result = {}
    result['dst'] = frame[0:6]
    result['src'] = frame[6:12]
    result['type'] = struct.unpack('>H', frame[12:12+2])[0]
    result['payload'] = frame[14:]
    return result

def parse_arp(packet):
    result = {}
    result['hw_type'] = struct.unpack('>H', packet[0:2])[0]
    result['proto_type'] = struct.unpack('>H', packet[2:4])[0]
    result['hw_size'] = struct.unpack('>B', packet[4:5])[0]
    result['proto_size'] = struct.unpack('>B', packet[5:6])[0]
    result['opcode'] = struct.unpack('>H', packet[6:8])[0]
    result['sender_mac'] = packet[8:14]
    result['sender_ip'] = packet[14:18]
    result['target_mac'] = packet[18:24]
    result['target_ip'] = packet[24:28]
    return result

def parse_ipv4(packet):
    result = {}
    result['ver_len'] = struct.unpack('>B', packet[0:1])[0]
    result['diff_svc_field'] = struct.unpack('>B', packet[1:2])[0]
    result['total_len'] = struct.unpack('>H', packet[2:4])[0]
    result['ident'] = struct.unpack('>H', packet[4:6])[0]
    result['flags'] = struct.unpack('>H', packet[6:8])[0]
    result['ttl'] = struct.unpack('>B', packet[8:9])[0]
    result['protocol'] = struct.unpack('>B', packet[9:10])[0]
    result['hdr_csum'] = struct.unpack('>H', packet[10:12])[0]
    result['src_addr'] = packet[12:16]
    result['dst_addr'] = packet[16:20]
    result['payload'] = packet[20:]
    return result

def parse_icmp(packet):
    result = {}
    result['type'] = struct.unpack('>B', packet[0:1])[0]
    result['code'] = struct.unpack('>B', packet[1:2])[0]
    result['csum'] = struct.unpack('>H', packet[2:4])[0]
    result['identifier'] = struct.unpack('>H', packet[4:6])[0]
    result['seq_num'] = struct.unpack('>H', packet[6:8])[0]
    result['timestamp'] = packet[8:16]
    result['data'] = packet[16:]
    return result

def mac2str(data):
    return f'{data[0]:02X}:{data[1]:02X}:{data[2]:02X}:{data[3]:02X}:{data[4]:02X}:{data[5]:02X}'

def ip2str(data):
    return f'{data[0]:d}.{data[1]:d}.{data[2]:d}.{data[3]:d}'

def str2ip(s):
    m = re.match(r'(\d+)\.(\d+)\.(\d+)\.(\d+)', s)
    return struct.pack('BBBB', int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)))

# this works for IP header and ICMP header
def calc_checksum(data):
    result = 0
    # add all the 2-byte words
    for i in range(0, len(data), 2):
        result += struct.unpack('!H', data[i:i+2])[0]
    # add any leftover byte
    if len(data) % 2:
        result += data[-1]
    # fold into 16 bits
    while result & 0xFFFF0000:
        result = (result >> 16) + (result & 0xFFFF)
    # complement, return
    result ^= 0xFFFF
    return result

def calc_checksum_h(data):
    return struct.pack('!H', calc_checksum(data))

def generate_mac():
    result = [random.randint(0, 255) for x in range(6)]
    result[0] |= 0x2 # setting the locally administered bit
    result[0] &= 0xFE # clearing the multicast bit
    result = b''.join(x.to_bytes(1, 'big') for x in result)
    return result

def connect(portA, portB):
    portA.destination = portB
    portB.destination = portA
