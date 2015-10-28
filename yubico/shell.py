#!/usr/bin/python
# mess around with the F2D-only (not OTP) yubico key promoted thru github

import os
import sys

# alib imports
sys.path.append(os.environ['PATH_ALIB_PY'])
import utils
from output import Info, Error, Warn, Debug, print_hex

import usb
from struct import pack, unpack
import readline
from binascii import hexlify

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

#------------------------------------------------------------------------------
# PACKET STUFF
#------------------------------------------------------------------------------
def pktSend(endPoint, data):
    Info("SENDING 0x%X (%d) bytes: " % (len(data), len(data)))
    print_hex(0, data)
    endPoint.write(data)

def pktRecv(endPoint):
    dataArray = endPoint.read(64)
    data = dataArray.tostring()
    Info("RECEIVED 0x%X (%d) bytes: " % (len(data), len(data)))
    print_hex(0, data)
    return data

#------------------------------------------------------------------------------
# MESSAGE STUFF
#------------------------------------------------------------------------------
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
            if len(self.payload) != 1:
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

if __name__ == '__main__':
    [dev, cfg, interf, endPointOut, endPointIn] = [None]*5
    # going with random command channel 1, use 'init' to alloc your own
    # but be aware of reconnect issues
    cidCommands = CID_RESERVED + 1

    while 1:
        line = raw_input('yubi> ').lower()

        if line == 'connect':
            # select device
            # `lsusb` gives: Bus 002 Device 012: ID 1050:0120 Yubico.com
            dev = usb.core.find(idVendor=YUBICO_VENDOR_ID, idProduct=NEO_SKY_PROD_ID)
            if dev is None: raise ValueError('Device not found')
       
            if dev.is_kernel_driver_active(0):
                Warn("detaching kernel HID driver")
                dev.detach_kernel_driver(0) 

            # set configuration to the first and only, retrieve it
            dev.set_configuration()
            cfg = dev.get_active_configuration()
            
            # get interface
            interf = cfg[(0,0)]
            
            # get endpoints
            (endpointOut, endpointIn) = interf.endpoints()
        
            print endpointOut
            print endpointIn
    
        elif line == 'ping':
            randData = utils.genRandomData(8)
            msg = Message(cidCommands, U2FHID_PING, randData)
            Info("PING!")
            msg.send(endpointOut)
            msg.recv(endpointIn)
            if msg.cmdId != U2FHID_PING:
                raise Exception("dongle did not respond with PING, got: %s" % str(msg))
            if len(msg.payload) != 8:
                raise Exception("dongle did not respond with 8-byte PING payload")
            if randData != msg.payload[0:8]:
                raise Exception("dongle did not match sent data in PING payload")
            Info("PONG!")

        elif line == 'init':
            # send some shit
            nonce = utils.genRandomData(8)
            print "nonce: " + hexlify(nonce)
            msg = Message(CID_BROADCAST, U2FHID_INIT, nonce)
            msg.send(endpointOut)
            print "COOL"
            msg.recv(endpointIn)

            if msg.cmdId != U2FHID_INIT:
                raise Exception("dongle did not respond with INIT, got: %s" % str(msg))
            msg.validate()
            nonceBack = msg.payload[0:8]
            if nonceBack != nonce:
                raise Exception("dongle did not match our nonce, got: %s" % repr(nonceBack))
            cidCommands = unpack('>I', msg.payload[8:12])[0]
            print "allocated command channel: 0x%X (%d)" % (cidCommands, cidCommands)
           
        elif line == 'wink':
            msg = Message(cidCommands, U2FHID_WINK, '')
            msg.send(endpointOut)
            msg.recv(endpointIn)

        elif line == 'quit':
            usb.util.dispose_resources(dev)
            usb.util.release_interface(dev, interf)
            break
            
    
