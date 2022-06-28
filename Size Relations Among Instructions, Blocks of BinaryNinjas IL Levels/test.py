#!/usr/bin/env python

# Q: Does
# A: yes

import os
import sys
import binaryninja

# returning number of instructions in a:
#  type                                            example source
#  ----                                            --------------
#  binaryninja.function.Function                   bv.get_function_at(0x100000f50)   
#  binaryninja.lowlevelil.LowLevelILFunction       func.lifted_il
#                                                  func.low_level_il
#                                                  func.low_level_il.ssa_form
#  binaryninja.mediumlevelil.MediumLevelILFunction func.medium_level_il
#                                                  func.medium_level_il.ssa_form
#  binaryninja.highlevelil.HighLevelILFunction     func.high_level_il
#                                                  func.high_level_il.ssa_form
#  
def counti(func):
    return sum([b.instruction_count for b in func])

def countb(func):
    return len(func.basic_blocks)

class relation(object):
    def __init__(self, description):
        self.description = description
        self.lt = True
        self.le = True
        self.eq = True
        self.ge = True
        self.gt = True

    def consume(self, func_a, func_b, a, b):
        if self.lt and a >= b:
            print(f'({self.description}) < disproved, counterexample: {func_a} has {a} >= {b}')
            self.lt = False
        if self.le and a > b:
            print(f'({self.description}) <= disproved, counterexample: {func_a} has {a} > {b}')
            self.le = False
        if self.eq and a != b:
            print(f'({self.description}) == disproved, counterexample: {func_a} has {a} != {b}')
            self.eq = False
        if self.ge and a < b:
            print(f'({self.description}) >= disproved, counterexample: {func_a} has {a} < {b}')
            self.ge = False
        if self.gt and a <= b:
            print(f'({self.description}) > disproved, counterexample: {func_a} has {a} <= {b}')
            self.gt = False

    def count_instrs(self, func_a, func_b):
        a,b = counti(func_a), counti(func_b)
        self.consume(func_a, func_b, a, b)

    def count_blocks(self, func_a, func_b):
        a,b = countb(func_a), countb(func_b)
        self.consume(func_a, func_b, a, b)

    def report(self):
        print(f'{self.description} REPORT:')
        if self.lt: print(f' <  holds')
        if self.le: print(f' <= holds')
        if self.eq: print(f' == holds')
        if self.ge: print(f' >= holds')
        if self.gt: print(f' >  holds')

files = []
if sys.argv[1:]:
    files = [sys.argv[1]]
else:
    import glob
    #files = glob.glob('~/fdumps/filesamples/busybox-*')
    files = glob.glob('/Users/andrewl/fdumps/filesamples/busybox-*')
    # keep files without extensions
    files = [f for f in files if os.path.splitext(f)[1] == '']

r0 = relation('asm vs. lifted instructions')
r0_b = relation('asm vs. lifted blocks')
r1 = relation('lifted vs. low instructions')
r1_b = relation('lifted vs. low blocks')
r2 = relation('low vs. low ssa instructions')
r2_b = relation('low vs. low ssa blocks')
r3 = relation('low vs. medium instructions')
r3_b = relation('low vs. medium blocks')
r4 = relation('medium vs. medium ssa instructions')
r4_b = relation('medium vs. medium ssa blocks')
r5 = relation('medium vs. high instructions')
r5_b = relation('medium vs. high blocks')
r6 = relation('high vs. high ssa instructions')
r6_b = relation('high vs. high ssa blocks')

for file in files:
    if '-m68k' in file or '-sparc' in file or '-sh4' in file:
        print(f'skipping: {file}')
        continue

    print(f'opening: {file}')
    bv = binaryninja.open_view(file)
    assert bv

    for func in bv.functions:
        # asm -> lifted
        r0.count_instrs(func, func.lifted_il)
        r0_b.count_blocks(func, func.lifted_il)

        # lifted -> low
        # low -> low ssa
        r1.count_instrs(func.lifted_il, func.low_level_il)
        r1_b.count_blocks(func.lifted_il, func.low_level_il)
        r2.count_instrs(func.low_level_il, func.low_level_il.ssa_form)
        r2_b.count_blocks(func.low_level_il, func.low_level_il.ssa_form)

        # low -> medium
        # medium -> medium ssa
        r3.count_instrs(func.low_level_il, func.medium_level_il)
        r3_b.count_blocks(func.low_level_il, func.medium_level_il)
        r4.count_instrs(func.medium_level_il, func.medium_level_il.ssa_form)
        r4_b.count_blocks(func.medium_level_il, func.medium_level_il.ssa_form)

        # medium -> high
        # high -> high ssa
        r5.count_instrs(func.medium_level_il, func.high_level_il)
        r5_b.count_blocks(func.medium_level_il, func.high_level_il)
        r6.count_instrs(func.high_level_il, func.high_level_il.ssa_form)
        r6_b.count_blocks(func.high_level_il, func.high_level_il.ssa_form)

print('--------')

print('for all these files:')
print('\n'.join(files))

print('--------')

for r in [r0, r1, r2, r3, r4, r5, r6]:
    r.report()

print('--------')

for r in [r0_b, r1_b, r2_b, r3_b, r4_b, r5_b, r6_b]:
    r.report()

