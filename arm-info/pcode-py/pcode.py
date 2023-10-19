#!/usr/bin/env python

import math
import enum

from helpers import *

#------------------------------------------------------------------------------
# 
#------------------------------------------------------------------------------

# to mimic the "bits(N)" type in the pcode
class BitsN(object):
    def __init__(self, value, N=None):
        self.value = value

        if N == None:
            N = math.ceil(math.log(self.value+1, 2)) if self.value else 0 # get bits required
            self.N = N - (N%4) + 4 if (N&3) else N # align to nearest 4
        else:
            self.N = N

    def msb(self):
        return (self.value >> (self.N-1)) & 1

    def lsb(self):
        return self.value & 1

    # eg: imm12<11:8> maps to imm12.slice(11, 8)
    def slice(self, msb, lsb):
        assert msb >= lsb
        width = msb - lsb + 1
        return BitsN((self.value >> lsb) & (2**width - 1), width)

    def __eq__(self, other):
        if type(other) == int:
            return self.value == other
        elif isinstance(other, BitsN):
            return self.value == other.value and self.N == other.N

    def __or__(self, other):
        return BitsN(self.value | other.value, max(self.N, other.N))

    def __str__(self):
        return f'0x{self.value:X}<{self.N:d}>'

# mirror the ":" operator
def concat(a, b):
    return BitsN((a.value << b.N) | b.value, a.N + b.N)

#------------------------------------------------------------------------------
# 
#------------------------------------------------------------------------------

# value: BitsN
def LSR(x, amount):
    return BitsN(bitshr(x.value, amount, x.N), x.N)

def LSL(x, amount):
    return BitsN(bitshl(x.value, amount, x.N), x.N)

class SRType(enum.Enum):
    LSL = 0
    LSR = 1
    ASR = 2
    ROR = 3
    RRX = 4

def LSL_C(value, amount):
    # TODO
    return None

def LSR_C(value, amount):
    # TODO
    return None

def ASR_C(value, amount):
    # TODO
    return None

# rotate right, and emit msb as carry out
def ROR_C(x:BitsN, shift:int):
    assert shift != 0
    m = shift % x.N
    result = LSR(x, m) | LSL(x, x.N-m)
    carry_out = result.msb()
    return (result, carry_out)

def RRX_C(value, amount):
    # TODO
    return None

def Zeros(N):
    return BitsN(0, N)

def ZeroExtend(x, N):
    assert N >= x.N
    return concat(Zeros(N - x.N), x)

# return a normal unsigned number from the BitsN
def UInt(x:BitsN):
    return x.value

# returns (<result>, <carry_out>) where width of result is width of value
#
# carry_in is only used when srtype RRX
# carry_out is set by internal shift or rotate
#
def Shift_C(value, srtype, amount, carry_in):
    if amount == 0:
        return (value, carry_in)
    
    match srtype:
        case SRType.LSL:
            return LSL_C(value, amount)
        case SRType.LSR:
            return LSR_C(value, amount)
        case SRType.ASR:
            return ASR_C(value, amount)
        case SRType.ROR:
            return ROR_C(value, amount)
        case SRType.RRX:
            return RRX_C(value, amount)

    breakpoint()

# returns 32-bits
def A32ExpandImm_C(imm12:BitsN, carry_in):
    unrotated_value = ZeroExtend(imm12.slice(7,0), 32)
    imm32, carry_out = Shift_C(unrotated_value, SRType.ROR, 2*UInt(imm12.slice(11,8)), carry_in)
    return (imm32, carry_out)

