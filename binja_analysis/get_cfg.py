#!/usr/bin/env python

import os, sys, re

import fizzbuzz
from helpers import *

(bv, func) = quick_get_func()

print('; function disassembly')
print_function_disasm(func)
graph_func('cfg_disassembly', func)

print('; lifted IL disassembly')
print_function_disasm(func.lifted_il)
graph_func('cfg_lifted_il', func.lifted_il)

print('; LLIL disassembly')
print_function_disasm(func.low_level_il)
graph_func('cfg_low_level_il', func.low_level_il)

print('; MLIL disassembly')
print_function_disasm(func.medium_level_il)
graph_func('cfg_medium_level_il', func.medium_level_il)

print('; HLIL disassembly')
print_function_disasm(func.high_level_il)
graph_func('cfg_high_level_il', func.high_level_il)
