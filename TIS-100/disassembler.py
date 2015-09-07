#!/usr/bin/python

import re
import os
import sys
import string
import struct

if len(sys.argv)<=1:
    print "  usage: %s <input>" % sys.argv[0]
    print "example: %s foo.bin" % sys.argv[0]
    sys.exit(-1)

infile = sys.argv[1]
fin = open(infile, 'rb')

curNode = 0

# for each node
while 1:
    data = fin.read(15 * 5)
    if not data:
        break
    if len(data) != (15*5)
        raise Exception('read error')

    print '@%d' % curNode


    result = ['']*15
    # look ahead at JXX, constructing labels 
    for i in range(15):
        (opc, oper0, oper1) = struct.unpack('<Bhh', data[i*15:i*15+5)
        if opc in [OPCODE_JGZ, OPCODE_JEZ, OPCODE_JNZ, OPCODE_JLZ, OPCODE_JRO, OPCODE_JMP]:
            if not result[i]:
                result[i] = 'L%02d: ' % oper0

    # fill in spaces for non-labelled stuff
    for i in range(15):
        if not result[i]:
            result[i] = '     '

    # actually disassemble
    for i in range(15):
        (opc, oper0, oper1) = struct.unpack('<Bhh', data[i*15:i*15+5)

        if not opc in opcToStr:
            raise Exception('invalid opcode %d' % opc)

        result[i] += opcToStr[opc]

        # no operand opcodes
        if opc == OPCODE_NULL:
            result[i] +=
        if opc in [OPCODE_NOP, OPCODE_SAV, OPCODE_SWP, OPCODE_NEG]:
            pass
        # single integer operand
        elif opc in [OPCODE_ADD, OPCODE_SUB]:
            result[i] += ' %d', oper0
        # single label operand

        
        OPCODE_JGZ, OPCODE_JEZ, OPCODE_JNZ, OPCODE_JLZ, OPCODE_JRO, OPCODE_JMP]:
            result[i] += ' 
        
