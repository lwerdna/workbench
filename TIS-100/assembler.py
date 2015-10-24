#!/usr/bin/python

import re
import os
import sys
import string
import struct

import defs

def assembleNode(fout, nodeLines):
    labelToAddr = {}

    # scan for labels, removing them
    for addr in range(len(nodeLines)):
        line = string.lstrip(nodeLines[addr])

        while 1:
            m = re.match(r'(\w+):.*', line)
            if not m: break
            label = m.group(1)
            labelToAddr[label] = addr
            print "set %s to address %d" % (label, addr)
            line = string.lstrip(line[len(label)+1:])

        nodeLines[addr] = line

    # add empty lines so that 15 instructions are assembled
    if len(nodeLines) > 15:
        raise Exception("node has more than 15 instructions!")
    nodeLines = nodeLines + ([""] * (15-len(nodeLines)))

    # now assemble
    for line in nodeLines:
        m = re.match(r'^(\w+) (.+?)(?:, (.+))?$', line)
        if m:
            mnem = m.group(1)
            opers = list(m.group(2, 3))
            opcode = None
    
            if mnem in defs.opcStrToId:
                opcode = defs.opcStrToId[mnem]
            else:
                raise Exception("unknown mnemonic \"%s\"" % mnem)
    
            # map text operand to id
            for i in range(len(opers)):
                if opers[i] == None:
                    opers[i] = 0
                elif re.match(r'-?\d+', opers[i]):
                    opers[i] = int(opers[i])
                elif opers[i] in labelToAddr:
                    opers[i] = labelToAddr[opers[i]]
                elif opers[i] in defs.operToId:
                    opers[i] = defs.operToId[opers[i]]
                else:
                    print "illegal operand \"%s\"" % opers[i]

            # write 'em 
            data = struct.pack('<Bhh', opcode, opers[0], opers[1])
            fout.write(data)

        elif re.match(r'^\s*$', line):
            data = struct.pack('<BHH', OPCODE_NULL, 0, 0)
            fout.write(data)

        else:
            print "syntax error for instruction \"%s\"" % line
            sys.exit(-1)

if len(sys.argv)<=1:
    print "  usage: %s <input> <output>" % sys.argv[0]
    print "example: %s foo.asm foo.bin" % sys.argv[0]
    sys.exit(-1)

infile = sys.argv[1]
outfile = sys.argv[2]

fin = open(infile, 'r')
fout = open(outfile, 'wb')

curLine = 0
curNode = -1
curProg = None
nodeLines = []
state = 'WAITING'

while 1:
    curLine += 1

    line = fin.readline()
    if not line: break
    line = string.rstrip(line)

    print "state=%s line=%d \"%s\"" % (state, curLine, line)

    # whitespace
    #
    if re.match(r'^\s*$', line):
        if state=='WAITING': 
            # waiting? whitespace means keep waiting
            continue

        if state=='INNODE':
            # in node? whitespace means the node is done
            print "writing node %d" % curNode
            assembleNode(fout, nodeLines)
            nodeLines = []
            state = 'WAITING'
            continue

    # node declarations eg: "@5"
    #
    m = re.match(r'@(\d)', line)
    if m:
        if state=='WAITING':
            # waiting? then we open a new node!
            nodeNum = int(m.group(1))
            if nodeNum != curNode+1:
                print "expected node %d (got %d)" % (curNode+1, nodeNum)
                sys.exit(-1)
            print "opening node %d" % nodeNum
            curNode = nodeNum
            state = 'INNODE'
            continue

        if state=='INNODE':
            # in node? expected whitespace to end it
            print "unexpected new node declaration within node %d" % curNode
            continue

    # ok what now?
    #
    if state=='WAITING':
        print "ERROR: don't know how to handle it, quiting..."
        break;
    elif state=='INNODE':
        # then assume it's an instruction or label
        nodeLines.append(line)
        continue

