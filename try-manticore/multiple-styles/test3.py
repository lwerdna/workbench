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
    print('A3B: set flag', state)
    with m.locked_context() as ctx:
        ctx['flag'] += chr(cpu.AL - 10)

@m.hook(0x400a21)
def hook(state):
    al = state.cpu.AL
    print(f'A21: al=', al)

@m.hook(0x400a2e)
def hook(state):
    al = state.cpu.AL
    print(f'A2E: al=', al)

@m.hook(0x400a31)
def hook(state):
    al = state.cpu.AL
    print(f'A31: al=', al)

@m.hook(0x400a34)
def hook(state):
    al = state.cpu.AL
    print(f'A34: al=', al)

@m.hook(0x400a3b)
def hook(state):
    al = state.cpu.AL
    print(f'A3B: al=', al)

@m.hook(0x400a3e)
def hook(state):
    print('A3E: setting ZF=1', state)
    cpu = state.cpu
    cpu.ZF = True

@m.hook(0x400a6c)
def hook(state):
    print("A6C: Success!", state)
    with m.locked_context() as ctx:
        print(ctx['flag'])
    m.kill()

m.run()
