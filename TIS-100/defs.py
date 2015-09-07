#!/usr/bin/python

import re
import os
import sys
import string
import struct

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

oprToStr = {
    OPER_ACC:'ACC', OPER_UP:'UP', OPER_DOWN:'DOWN', OPER_RIGHT:'RIGHT', OPER_LEFT:'LEFT'
}

# in python:
# (
# struct program {
#     struct instruction instrs[15];
# }

# struct system {
#     struct program prgrms[9];
# }
#

strToOpc = { 
    'NOP':OPCODE_NOP, 'SAV':OPCODE_SAV, 'SWP':OPCODE_SWP,
    'ADD':OPCODE_ADD, 'SUB':OPCODE_SUB, 'NEG':OPCODE_NEG,
    'MOV':OPCODE_MOV, 'JGZ':OPCODE_JGZ, 'JEZ':OPCODE_JEZ,
    'JNZ':OPCODE_JNZ, 'JLZ':OPCODE_JLZ, 'JRO':OPCODE_JRO,
    'JMP':OPCODE_JMP
}
   
opcToStr = {
    OPCODE_NOP:'NOP', OPCODE_SAV:'SAV', OPCODE_SWP:'SWP',
    OPCODE_ADD:'ADD', OPCODE_SUB:'SUB', OPCODE_NEG:'NEG',
    OPCODE_MOV:'MOV', OPCODE_JGZ:'JGZ', OPCODE_JEZ:'JEZ',
    OPCODE_JNZ:'JNZ', OPCODE_JLZ:'JLZ', OPCODE_JRO:'JRO',
    OPCODE_JMP:'JMP'
}


