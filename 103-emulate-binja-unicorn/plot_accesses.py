#!/usr/bin/env python

import matplotlib.pyplot as plt

read_xs = []
read_ys = []
with open('stack_reads.txt') as fp:
    for line in fp.readlines():
        instr, addr = line.strip().split()
        read_xs.append(int(instr))
        read_ys.append(int(addr, 16))

write_xs = []
write_ys = []
with open('stack_writes.txt') as fp:
    for line in fp.readlines():
        instr, addr = line.strip().split()
        write_xs.append(int(instr))
        write_ys.append(int(addr, 16))

plt.plot(read_xs, read_ys, color='#00FF00', marker='o', linestyle='none')
plt.plot(write_xs, write_ys, color='#FF0000', marker='o', linestyle='none')

axes = plt.gca()
#axes.invert_yaxis()
#ylabels = map(lambda t: '0x%08X' % int(t), axes.get_yticks())
#axes.set_yticklabels(ylabels)

#plt.savefig('plot.svg')
plt.show()
