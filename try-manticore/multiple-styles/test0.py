#!/usr/bin/env python

# just print the blocks as the state explores them

from manticore.native import Manticore

m = Manticore('./multiple-styles')

@m.hook(0x4009ae)
def hook(state):
    print('40009ae: main', state)

@m.hook(0x400a55)
def hook(state):
    print('400a55: top of loop, calls strlen()', state)

@m.hook(0x400a17)
def hook(state):
    print('400a17: looks at byte', state)

@m.hook(0x400a51)
def hook(state):
    print('400a51: increments loop counter', state)

@m.hook(0x400a6c)
def hook(state):
    print('400a6c: SUCCESS', state)

@m.hook(0x400a40)
def hook(state):
    print('400a40: FAILURE', state)

@m.hook(0x400a7b)
def hook(state):
    print('400a7b: end block 1/3, stack check', state)

@m.hook(0x400a8f)
def hook(state):
    print('400a8f: end block 2/3, stack check ok', state)

@m.hook(0x400a8a)
def hook(state):
    print('400a8a, end block 3/3, stack check fail', state)

m.run()
