#!/usr/bin/env python

# is LLIL/MLIL/HLIL saved and available after .bndb load?

import binaryninja

def print_func(f):
    print('LOW:')
    for block in f.low_level_il:
        for insn in block:
            print(insn)
    print('MEDIUM:')
    for block in f.medium_level_il:
        for insn in block:
            print(insn)
    print('HIGH:')
    for block in f.high_level_il:
        for insn in block:
            print(insn)

data = b'\x55\x48\x89\xe5\x89\x7d\xfc\x48\x89\x75\xf0\xb8\x00\x00\x00\x00\x5d\xc3'

plat = binaryninja.Platform['linux-x86_64']
bv = binaryninja.binaryview.BinaryView.new(data)
bv.platform = plat
bv.add_function(0, plat=plat)
bv.update_analysis_and_wait()

assert len(bv.functions)==1
f = bv.functions[0]
print('IL available after creation:')
print_func(f)

bv.create_database('/tmp/tmp.bndb')

print('-------- IL available from .bndb with get_view_of_file(update_analysis=False)')
bv = binaryninja.BinaryViewType.get_view_of_file('/tmp/tmp.bndb', update_analysis=False)
assert len(bv.functions)==1
f = bv.functions[0]
print_func(f)

print('-------- IL available from .bndb with get_view_of_file(update_analysis=True)')
bv = binaryninja.BinaryViewType.get_view_of_file('/tmp/tmp.bndb', update_analysis=True)
assert len(bv.functions)==1
f = bv.functions[0]
print_func(f)

print('-------- IL available from .bndb with open_view()')
with binaryninja.open_view('/tmp/tmp.bndb') as bv:
    assert len(bv.functions)==1
    f = bv.functions[0]
    #f.reanalyze()
    print_func(f)

