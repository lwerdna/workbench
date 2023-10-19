#!/usr/bin/env python

from pcode import *

for cin in [0, 1]:
    for imm12 in range(0x1000):
        imm32, cout = A32ExpandImm_C(BitsN(imm12, 12), 1)
        
        if cin != cout:
            print(f'imm12=0x{imm12:04X} cin={cin}  has  imm32={imm32} cout={cout}')

        if cout != imm32.msb():
            breakpoint()
