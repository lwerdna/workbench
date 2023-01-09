#!/usr/bin/env python

# concrete-solve.py from:
# https://gist.github.com/ehennenfent/a5ad9746615d1490c618a88b98769c10
# updated to latest Manticore

from manticore.native import Manticore

m = Manticore('./multiple-styles')
m.context['flag'] = ""

@m.hook(0x400a3b)
def hook(state):
    cpu = state.cpu
    print('set flag')
    with m.locked_context() as ctx:
        ctx['flag'] += chr(cpu.AL - 10)

@m.hook(0x400a3e)
def hook(state):
    print('setting ZF=1')
    cpu = state.cpu
    cpu.ZF = True

@m.hook(0x400a40)
def hook(state):
    #print("Failed")
    m.kill()

@m.hook(0x400a6c)
def hook(state):
    print("Success!")
    with m.locked_context() as ctx:
        print(ctx['flag'])
    m.kill()

m.run()
