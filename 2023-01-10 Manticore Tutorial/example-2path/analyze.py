#!/usr/bin/env python

from manticore.native import Manticore

m = Manticore('./example')

@m.hook(0x201160)
def hook(state):
    print('201160', state)

# right before jg
@m.hook(0x201184)
def hook(state):
    print(f'{hex(state.cpu.RIP)}: {state}')
    expr = state.cpu.AL
    print(f'{hex(state.cpu.RIP)}: al is {expr} with possible solution {state.solve_one(expr)}')

# stdin[0] > 0x80
@m.hook(0x2011a3)
def hook(state):
    print(f'{hex(state.cpu.RIP)}: {state}')
    expr = state.cpu.AL
    print(f'{hex(state.cpu.RIP)}: al is {expr} with possible solution {state.solve_one(expr)}')

# stdin[0] <= 0x80
@m.hook(0x201186)
def hook(state):
    print(f'{hex(state.cpu.RIP)}: {state}')
    expr = state.cpu.AL
    print(f'{hex(state.cpu.RIP)}: al is {expr} with possible solution {state.solve_one(expr)}')

@m.hook(0x2011c0)
def hook(state):
    print(f'{hex(state.cpu.RIP)}: {state}')

m.run()
