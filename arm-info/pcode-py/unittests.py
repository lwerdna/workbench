#!/usr/bin/env python

from pcode import *

if __name__ == '__main__':
    assert(bitshl(0xDEADBEEF, 8) == 0xADBEEF00)
    assert(bitshr(0xDEADBEEF, 8) == 0x00DEADBE)
    assert(bitrol(0xDEADBEEF, 4) == 0xEADBEEFD)
    assert(bitror(0xDEADBEEF, 4) == 0xFDEADBEE)

    assert(bitshl(0xDEAD, 4, 16) == 0xEAD0)
    assert(bitshr(0xDEAD, 4, 16) == 0x0DEA)
    assert(bitrol(0xABCD, 4, 16) == 0xBCDA)
    assert(bitror(0xABCD, 4, 16) == 0xDABC)

    assert(LSR(BitsN(0xDEAD, 16), 4) == 0x0DEA)
    
    assert(BitsN(0b00000) == BitsN(0, 0))

    assert(BitsN(0b00001) == BitsN(1, 4))
    assert(BitsN(0b00011) == BitsN(3, 4))
    assert(BitsN(0b00111) == BitsN(7, 4))
    assert(BitsN(0b01111) == BitsN(15, 4))
    assert(BitsN(0b11111) == BitsN(31, 8))

    assert(Zeros(2) == BitsN(0, 2))
    assert(Zeros(7) == BitsN(0, 7))
    assert(Zeros(17) == BitsN(0, 17))

    assert(ZeroExtend(BitsN(0xD), 16) == BitsN(0xD, 16))
    assert(ZeroExtend(BitsN(0xAD), 17) == BitsN(0xAD, 17))
    assert(ZeroExtend(BitsN(0xEAD), 18) == BitsN(0xEAD, 18))
    assert(ZeroExtend(BitsN(0xDEAD), 19) == BitsN(0xDEAD, 19))

    assert(BitsN(0b1101111010101101).slice(0,0) == BitsN(0b1, 1))
    assert(BitsN(0b1101111010101101).slice(1,0) == BitsN(0b01, 2))
    assert(BitsN(0b1101111010101101).slice(7,0) == BitsN(0b10101101, 8))
    assert(BitsN(0b1101111010101101).slice(13,0) == BitsN(0b1111010101101, 14))
    #assert(LSR(BitsN(0xDEAD, 16), 4) == 0x0DEA)


