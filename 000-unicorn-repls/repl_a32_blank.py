#!/usr/bin/env python

# an assembly REPL for aarch32 execution environment (A32/T32 instruction sets)

from unicorn import *
from unicorn.arm_const import *

import aarch32

CODE_MEM_START = 0
CODE_MEM_LENGTH = 2**16
STACK_MEM_START = 0xFFFF0000
STACK_MEM_LENGTH = 2**16

uc = Uc(UC_ARCH_ARM, UC_MODE_ARM + UC_MODE_LITTLE_ENDIAN)

uc.mem_map(CODE_MEM_START, CODE_MEM_LENGTH)
uc.mem_map(STACK_MEM_START, STACK_MEM_LENGTH)
uc.reg_write(UC_ARM_REG_PC, CODE_MEM_START)
uc.reg_write(UC_ARM_REG_SP, STACK_MEM_START + STACK_MEM_LENGTH)

aarch32.repl(uc)
