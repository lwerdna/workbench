#!/usr/bin/env python

import os, sys, re

from helpers import *

import binaryninja
from binaryninja.binaryview import BinaryViewType

fpath = sys.argv[1]
symbol = sys.argv[2]

bv = BinaryViewType.get_view_of_file(fpath)
bv.update_analysis_and_wait()
func = bv.get_functions_by_name(symbol)[0]

#breakpoint()

addrs = get_instruction_addresses(func)

#for addr in addrs:
#    print('%08X:' % addr)
#    print('\t%s' % get_lifted_il_at(bv, addr))
#    print('\t%s' % get_llil_at(bv, addr))
#    print('\t%s' % get_mlil_at(bv, addr))
#    print('\t%s' % get_hlil_at(bv, addr))
#
#print('----')
#
#for addr in addrs:
#    a = [str(x) for x in get_lifted_il_at(bv, addr)]
#    b = [str(x) for x in get_llil_at(bv, addr)]
#    c = [str(x) for x in get_mlil_at(bv, addr)]
#    d = [str(x) for x in get_hlil_at(bv, addr)]
#
#    (a,b,c,d) = [str(x or 'None').rjust(32) for x in 
#        [get_lifted_il_at(bv, addr), get_llil_at(bv, addr), get_mlil_at(bv, addr), get_hlil_at(bv, addr)]
#    ]
#    print('%08X: %s%s%s%s' % (addr, a,b,c,d))

# addr: location of lifted il
#    i: index into possibly multiple IL instructions at <addr>
def lifted_il_node_name(addr, i):
    return 'lifted_il_%08X_%d' % (addr, i)

def llil_node_name(addr, i):
    return 'llil_%08X_%d' % (addr, i)

def mlil_node_name(addr, i):
    return 'mlil_%08X_%d' % (addr, i)

def hlil_node_name(addr, i):
    return 'hlil_%08X_%d' % (addr, i)

print('digraph G {')
#print('\trankdir=LR;')

# assembler
print('\tsubgraph cluster_asm {')
print('\t\t{')
for addr in addrs:
    node_name = 'asm_%08X' % addr
    print('\t\t\t%s [shape="box" color="red" label="%08X: %s"]' % (node_name, addr, get_disassembly_at(bv, addr)))
print('\t\t}')
for (i, addr) in enumerate(addrs):
    if i==len(addrs)-1: break
    src = 'asm_%08X' % addr
    dst = 'asm_%08X' % addrs[i+1]
    print('\t\t%s -> %s' % (src, dst))
print('\t}')

# lifted IL
print('\tsubgraph cluster_lifted_il {')
print('\t\t{')
#print('\t\t\trank=same;')
infos = [] # list of (<addr>, <i>) where <i> is index into possibly multiple instructions at <addr>
for addr in addrs:
    infos.extend([(addr, i) for i in range(len(get_lifted_il_at(bv, addr)))])
for (addr, i) in infos:
    name = lifted_il_node_name(addr, i)
    label = '%08X: %s' % (addr, str(get_lifted_il_at(bv, addr)[i]))
    print('\t\t\t%s [shape="box" color="blue" label="%s"]' % (name, label))
print('\t\t}')
for ((addr_a, index_a), (addr_b, index_b)) in zip(infos[:-1], infos[1:]):
    name_a = lifted_il_node_name(addr_a, index_a)
    name_b = lifted_il_node_name(addr_b, index_b)
    print('\t\t%s -> %s' % (name_a, name_b))
print('\t}')

# low level IL
print('\tsubgraph cluster_llil {')
print('\t\t{')
infos = [] # list of (<addr>, <i>) where <i> is index into possibly multiple instructions at <addr>
for addr in addrs:
    infos.extend([(addr, i) for i in range(len(get_llil_at(bv, addr)))])
for (addr, i) in infos:
    name = llil_node_name(addr, i)
    label = '%08X: %s' % (addr, str(get_llil_at(bv, addr)[i]))
    print('\t\t\t%s [shape="box" color="green" label="%s"]' % (name, label))
print('\t\t}')
for ((addr_a, index_a), (addr_b, index_b)) in zip(infos[:-1], infos[1:]):
    name_a = llil_node_name(addr_a, index_a)
    name_b = llil_node_name(addr_b, index_b)
    print('\t\t%s -> %s' % (name_a, name_b))
print('\t}')

# medium level IL
print('\tsubgraph cluster_mlil {')
print('\t\t{')
infos = [] # list of (<addr>, <i>) where <i> is index into possibly multiple instructions at <addr>
for addr in addrs:
    infos.extend([(addr, i) for i in range(len(get_mlil_at(bv, addr)))])
for (addr, i) in infos:
    name = mlil_node_name(addr, i)
    label = '%08X: %s' % (addr, str(get_mlil_at(bv, addr)[i]))
    print('\t\t\t%s [shape="box" color="darkorange" label="%s"]' % (name, label))
print('\t\t}')
for ((addr_a, index_a), (addr_b, index_b)) in zip(infos[:-1], infos[1:]):
    name_a = mlil_node_name(addr_a, index_a)
    name_b = mlil_node_name(addr_b, index_b)
    print('\t\t%s -> %s' % (name_a, name_b))
print('\t}')

# HLIL
print('\tsubgraph cluster_hlil {')
print('\t\t{')
infos = [] # list of (<addr>, <i>) where <i> is index into possibly multiple instructions at <addr>
for addr in addrs:
    infos.extend([(addr, i) for i in range(len(get_hlil_at(bv, addr)))])
for (addr, i) in infos:
    name = hlil_node_name(addr, i)
    label = '%08X: %s' % (addr, str(get_hlil_at(bv, addr)[i]))
    print('\t\t\t%s [shape="box" color="darkorchid" label="%s"]' % (name, label))
print('\t\t}')
for ((addr_a, index_a), (addr_b, index_b)) in zip(infos[:-1], infos[1:]):
    name_a = hlil_node_name(addr_a, index_a)
    name_b = hlil_node_name(addr_b, index_b)
    print('\t\t%s -> %s' % (name_a, name_b))
print('\t}')

# assembler -> lifted IL
# one-to-many
for addr in addrs:
    src = 'asm_%08X' % addr
    for i in range(len(get_lifted_il_at(bv, addr))):
        dst = lifted_il_node_name(addr, i)
        print('\t%s -> %s' % (src, dst))
# lifted -> LLIL
# many-to-one
# addr x maps to next available LLIL addr y such that y>=x
for addr in addrs:
    lifted = get_lifted_il_at(bv, addr)
    if not lifted: continue

    llil_addr = next(a for a in addrs if a>=addr and get_llil_at(bv, a))
    
    for i in range(len(lifted)):
        src = lifted_il_node_name(addr, i)
        dst = llil_node_name(llil_addr, 0)
        print('\t%s -> %s' % (src, dst))
# LLIL -> MLIL
# many-to-one
# addr x maps to next available MLIL addr y such that y>=x
for addr in addrs:
    llil = get_llil_at(bv, addr)
    if not llil: continue

    #if addr == 0x8d8:
    #    breakpoint()
    mlil_addr = next(a for a in addrs if a>=addr and get_mlil_at(bv, a))
    
    for i in range(len(llil)):
        src = llil_node_name(addr, i)
        dst = mlil_node_name(mlil_addr, 0)
        print('\t%s -> %s' % (src, dst))
# MLIL -> HLIL
# many-to-one
# addr x maps to next available HLIL addr y such that y>=x
for addr in addrs:
    mlil = get_mlil_at(bv, addr)
    if not mlil: continue

    #if addr == 0x8d8:
    #    breakpoint()
    hlil_addr = next(a for a in addrs if a>=addr and get_hlil_at(bv, a))
    
    for i in range(len(mlil)):
        src = mlil_node_name(addr, i)
        dst = hlil_node_name(hlil_addr, 0)
        print('\t%s -> %s' % (src, dst))
print('}')

