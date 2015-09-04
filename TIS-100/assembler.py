#!/usr/bin/python

import re
import os
import sys


# in python:
# (opcode, operand0, operand1)
# in C:
# struct instruction {
#    uint8_t opcode;
#    uint16_t operand0;
#    uint16_t operand1;
# }
#

OPCODE_NULL = 0 # indicates no instruction present at all

OPCODE_NOP = 1

OPCODE_SAV = 2
OPCODE_SWP = 3

OPCODE_ADD = 4
OPCODE_SUB = 5
OPCODE_NEG = 6

OPCODE_MOV = 7

OPCODE_JGZ = 8
OPCODE_JEZ = 9
OPCODE_JNZ = 10
OPCODE_JLZ = 11
OPCODE_JRO = 12 # JRO <reg> 
OPCODE_JMP = 13 # JRO <imm> assembles to this

# operands can be immediates, labels, or the below fixed items:
# immediates are in [-999,999]
# labels end up as imm [0,15] 
# and the below element stay out of the imm band:
OPER_ACC = 1000
OPER_UP = 1001
OPER_DOWN = 1002
OPER_RIGHT = 1003
OPER_LEFT = 1004

# in python:
# (
# struct program {
#     struct instruction instrs[15];
# }

# struct system {
#     struct program prgrms[9];
# }
#

def assembleNode(fout, instrs):
    labelToAddr:

    # scan for labels:
    for instr in instrs:
        if re.match(r'(\w+):.*', instr)
            label

    # now assemble

    for instr in instrs:
        m = re.match(r'(.+) (.+)(?, (.+))?', line)
        if not m:
        if m:
            mnem = m.group(1)
            opers = [m.group(2)]
            if m.group(3): opers.append(m.group(3))
    
            opcStrToId = { 
                'NOP':OPCODE_NOP, 'SAV':OPCODE_SAV, 'SWP':OPCODE_SWP,
                'ADD':OPCODE_ADD, 'SUB':OPCODE_SUB, 'NEG':OPCODE_NEG,
                'MOV':OPCODE_MOV, 'JGZ':OPCODE_JGZ, 'JEZ':OPCODE_JEZ,
                'JNZ':OPCODE_JNZ, 'JLZ':OPCODE_JLZ, 'JRO':OPCODE_JRO,
                'JMP':OPCODE_JMP
            }
    
            if mnem not in opcStrToId:
                raise Exception("unknown mnemonic \"%s\"" % mnem)
    
            operToId = {
                'ACC':OPER_ACC, 'UP':OPER_UP, 'DOWN':OPER_DOWN, 
                'LEFT':OPER_LEFT, 'RIGHT':OPER_RIGHT
            }
    
            for oper in opers:
                if not re.match(r'-?\d+', oper) and \
                    not oper in curLabels and \
                    not oper in operToId:
    
                    print "illegal operand \"%s\"" % oper

            for instr in curProg:
                (opcode, oper0, oper1) = instr;
                data = pack('<BHH', opcode, oper0, oper1)
                fout.write(data)
            numEmpty = 15-len(curProg)
            print "on node %d filling %d null instructions" % (curNode, numEmpty)
            for i in range(numEmpty):
                data = pack('<BHH', OPCODE_NULL, 0, 0)
                fout.write(data)


if len(sys.argv)<=1:
    print "  usage: %s <input> <output>" % sys.argv[0]
    print "example: %s foo.asm foo.bin" % sys.argv[0]
    sys.exit(-1)

infile = sys.argv[1]
outfile = sys.argv[2]

fin = open(infile, 'r')
fout = open(outfile, 'wb')

curLine = 0
curNode = 0
curProg = None
curInstrs = []
state = 'WAITING'
state = 'INNODE'

while 1:
    curLine += 1
    line = f.readline()
    if not line: break

    # whitespace
    #
    if re.match(r'\s*', line):
        if state=='WAITING': 
            # waiting? whitespace means keep waiting
            pass
        if state=='INNODE':
            # in node? whitespace means the node is done
            print "writing node %d" % curNode
        continue

    # node declarations eg: "@5"
    #
    m = re.match(r'@(\d)')
    if m:
        if state=='WAITING':
            # waiting? then we open a new node!
            nodeNum = int(m.group(1))
            if nodeNum != curNode+1:
                print "expected node %d (got %d)" % (curNode+1, nodeNum)
                sys.exit(-1)
            print "opening node %d" % nodeNum
            curNode = nodeNum
        if state=='INNODE':
            # in node? expected whitespace to end it
            print "unexpected new node declaration within node %d" % curNode
        continue

    # actual instructions
    #
    m = re.match(r'(.+) (.+)(?, (.+))?', line)
    if m:
        curInstrs.append(line)






                
            






