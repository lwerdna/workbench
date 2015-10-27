#!/usr/bin/python
# mess around with the F2D-only (not OTP) yubico key promoted thru github

# protocol stack:
# +------------------+
# | U2F              | TRANSACTIONS
# |                  | (encapsulated in U2FHID_MSG)
# |                  |
# +------------------+ 
# | U2FHID           | MESSAGES
# |                  | - logical channels: 0 (reserved), ..., 0xFFFFFFFF (broadcast)
# |                  | - commands: U2FHID_INIT, U2FHID_PING, U2FHID_WINK
# |                  | - initialization and continuation packets
# +------------------+
# | USB REPORT       | PACKETS
# |                  | - IN and OUT endpoints
# |                  | - 64-byte chunks (HID_RPT_SIZE)
# +------------------+
# | USB              |
# +------------------+
#

# find docs with `pydoc usb` or within python `help(usb)`
# code for me is in /usr/local/lib/python2.7/dist-packages/pyusb-1.0.0b2-py2.7.egg (treat like zip file)

import usb
from struct import pack, unpack

#------------------------------------------------------------------------------
# PROTOCOL CONSTANTS
#------------------------------------------------------------------------------
YUBICO_VENDOR_ID = 0x1050
NEO_SKY_PROD_ID = 0x120
MAX_PKT_SIZE = 64
MAX_PKT_INIT_SIZE = MAX_PKT_SIZE - 7
MAX_PKT_CONT_SIZE = MAX_PKT_SIZE - 5
LOGICAL_CHAN_ID = 0

ENDPOINT_ADDR_OUT = 0x04
ENDPOINT_ADDR_IN = 0x84

# see fido-u2f-u2f.h and fido-u2f-u2fhid.h
TYPE_INIT = 0x80
U2FHID_PING = (TYPE_INIT | 0x01)	
U2FHID_MSG = (TYPE_INIT | 0x03)	
U2FHID_LOCK = (TYPE_INIT | 0x04)	
U2FHID_INIT = (TYPE_INIT | 0x06)	
U2FHID_WINK = (TYPE_INIT | 0x08)	
U2FHID_ERROR = (TYPE_INIT | 0x3f)	
U2FHID_VENDOR_FIRST = (TYPE_INIT | 0x40)	
U2FHID_VENDOR_LAST = (TYPE_INIT | 0x7f)	

CID_RESERVED = 0
CID_BROADCAST = 0xFFFFFFFF

ERR_NONE = 0x00	
ERR_INVALID_CMD = 0x01	
ERR_INVALID_PAR = 0x02	
ERR_INVALID_LEN = 0x03	
ERR_INVALID_SEQ = 0x04	
ERR_MSG_TIMEOUT = 0x05	
ERR_CHANNEL_BUSY = 0x06	
ERR_LOCK_REQUIRED = 0x0a	
ERR_INVALID_CID = 0x0b	
ERR_OTHER = 0x7f	

CAPFLAG_WINK = 1
CAPFLAG_LOCK = 2

def pktSend(endPoint, data):
    print "SENDING 0x%X (%d) bytes: " % (len(data), len(data)) + repr(data)
    endPoint.write(data)

def pktRecv(endPoint):
    dataArray = endPoint.read(64)
    data = dataArray.tostring()
    print "RECEIVED 0x%X (%d) bytes: " % (len(data), len(data)) + repr(data)
    return data

class Message():
    def __init__(self, chanId=CID_BROADCAST, cmdId=U2FHID_PING, payload=''):
        self.chanId = chanId
        self.cmdId = cmdId
        self.payload = payload

    def recv(self, endPoint):
        self.payload = ''

        data = pktRecv(endPoint)
        (self.chanId, self.cmdId) = unpack('IB', data[0:5])
        data = data[5:]
        lenRemaining = unpack('>H', data[0:2])[0]
        print repr(lenRemaining)
        data = data[2:]
        
        chunkSize = min(MAX_PKT_INIT_SIZE, lenRemaining)
        self.payload += data[0:chunkSize]
        lenRemaining -= chunkSize
   
        seqExpect = 0
        while lenRemaining:
            data = pktRecv(endPoint)
            (cid, seq) = unpack('IB', data[0:5])
            if cid != self.chanId:
                print 'ERROR: continuation packet cid (%d) != initialization packet cid (%d)' % \
                    (cid, self.chanId)                
            if seq != seqExpect:
                print 'ERROR: continuation packet seq (%d) != expected seq (%d)' % \
                    (seq, seqExpect)

            data = data[5:]
    
            chunkSize = min(MAX_PKT_CONT_SIZE, lenRemaining)
            self.payload += data[0:chunkSize]
            lenRemaining -= chunkSize

            seqExpect += 1

    # send a message
    # message = initialization_pkt [ + continuation_pkt ...]
    def send(self, endPoint):
        data = self.payload

        seq = 0
        lenRemaining = len(data)
        chunkSize = 0
    
        # CONSTRUCT, SEND FIRST PACKET
        #
        # Offset    Length    Mnemonic    Description
        # 0         4         CID         Channel identifier
        # 4         1         CMD         Command identifier (bit 7 always set)
        # 5         1         BCNTH       High part of payload length
        # 6         1         BCNTL       Low part of payload length
        # 7         (s - 7)   DATA        Payload data (s is equal to the fixed packet size)
        chunkSize = min(MAX_PKT_INIT_SIZE, len(data))
    
        pktInit = ''
        pktInit += pack('IB', self.chanId, self.cmdId)
        pktInit += pack('>H', chunkSize)
        pktInit += data[0:chunkSize]
        lenRemaining -= chunkSize
    
        pktInit += '\x00'*(MAX_PKT_SIZE - len(pktInit))
        pktSend(endPoint, pktInit)
    
        # CONSTRUCT, SEND REMAINING PACKETS (IF NECESSARY)
        #
        # Offset    Length    Mnemonic    Description
        # 0         4         CID         Channel identifier
        # 4         1         SEQ         Packet sequence 0x00..0x7f (bit 7 always cleared)
        # 5         (s - 5)   DATA        Payload data (s is equal to the fixed packet size)
        while lenRemaining:
            chunkSize = min(MAX_PKT_CONT_SIZE, len(data))
    
            pktCont = ''
            pktCont += pack('IB', self.chanId, seq)
            pktCont += data[0:chunkSize]
            lenRemaining -= chunkSize
    
            pktCont += '\x00'*(MAX_PKT_SIZE - len(pktCont))
            pktSend(endPoint, pktCont)
            seq += 1

    def validate(self, throw=True):
        rc = True

        if self.cmdId == U2FHID_INIT:
            if self.chanId != CID_BROADCAST:
                if throw: raise Exception('init message on non-broadcast channel (%d)' % self.chanId)
                rc = False
            if len(self.payload) != 17:
                if throw: raise Exception('init message should have 17 byte payload')
                rc = False
    
        elif self.cmdId == U2FHID_WINK:
            if len(self.payload) != 0:
                if throw: raise Exception('wink msg should have no data')
                rc = False
    
        elif self.cmdId == U2FHID_ERROR:
            if len(data) != 1:
                if throw: raise Exception('error msg should have 1 byte of data')
                rc = False

        return rc

    def __str__(self):
        self.validate()
  
        if self.cmdId == U2FHID_INIT:
            (nonce, chanAlloc, protVer, devVerMaj, devVerMin, buildDevVer, capFlags) = \
                unpack('>QIBBBBB', self.payload)

            res = 'msg cmd=U2FHID_INIT chAlloc=%d protVer=%d devVer=%d.%d buildVer=%d capFlags=%d' % \
                (chanAlloc, protVer, devVerMaj, devVerMin, buildDevVer, capFlags)

            if capFlags:
                res += '('
                if capFlags & CAPFLAG_WINK: res += 'WINK'
                if capFlags & CAPFLAG_LOCK: res += 'LOCK'
                res += ')'

            return res
    
        if self.cmdId == U2FHID_LOCK:
            return 'msg cmd=U2FHID_LOCK'
    
        if self.cmdId == U2FHID_WINK:
            return 'msg cmd=U2FHID_WINK'

        elif self.cmdId == U2FHID_ERROR:
            res = 'msg cmd=U2FHID_ERROR'

            code = unpack('B', data[0])[0]
            res += " code=%d" % code
    
            if code == ERR_NONE: res += ' (ERR_NONE)'
            elif code == ERR_INVALID_CMD: res += ' (ERR_INVALID_CMD)'
            elif code == ERR_INVALID_PAR: res += ' (ERR_INVALID_PAR)'
            elif code == ERR_INVALID_LEN: res += ' (ERR_INVALID_LEN)'
            elif code == ERR_INVALID_SEQ: res += ' (ERR_INVALID_SEQ)'
            elif code == ERR_MSG_TIMEOUT: res += ' (ERR_MSG_TIMEOUT)'
            elif code == ERR_CHANNEL_BUSY: res += ' (ERR_CHANNEL_BUSY)'
            elif code == ERR_LOCK_REQUIRED: res += ' (ERR_LOCK_REQUIRED)'
            elif code == ERR_INVALID_CID: res += ' (ERR_INVALID_CID)'
            elif code == ERR_OTHER: res += ' (ERR_OTHER)'
            else: res += ' (unknown)'
   
            return res

        else:
            return 'msg cmd=(unknown)'

# `lsusb` to find your device
# `lsusb -v -d 1050:0120` for details:
# device descr (Bus 002 Device 012: ID 1050:0120 Yubico.com)
#   config descr
#     interface descr (class: HID)
#       endpoint descr (addr: 0x04 EP 4 OUT) (pkt size: 64)
#       endpoint descr (addr: 0x84 EP 4 IN)  (pkt size: 64)

# select device
# `lsusb` gives: Bus 002 Device 012: ID 1050:0120 Yubico.com
dev = usb.core.find(idVendor=YUBICO_VENDOR_ID, idProduct=NEO_SKY_PROD_ID)
if dev is None: raise ValueError('Device not found')

# set configuration to the first and only, retrieve it
#dev.set_configuration()
cfg = dev.get_active_configuration()

# get interface
interf = cfg[(0,0)]

# get endpoints
(endpointOut, endpointIn) = interf.endpoints()

print endpointOut
print endpointIn

# send some shit
msg = Message(CID_BROADCAST, U2FHID_INIT, "\x01\x02\x03\x04\xAA\xBB\xCC\xDD")
msg.send(endpointOut)
msg.recv(endpointIn)
print msg

#msgSend(dev, U2FHID_PING, "\xDE\xAD\xBE\xEF")
#resp = dev.read(ENDPOINT_ADDR_IN, 64)
#print repr(resp)

