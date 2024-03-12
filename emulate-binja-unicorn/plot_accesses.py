#!/usr/bin/env python

import matplotlib.pyplot as plt

xs = []
ys = []

with open('stack_writes.txt') as fp:
    for line in fp.readlines():
        instr, addr = line.strip().split()

        xs.append(int(instr))
        ys.append(int(addr, 16))

#print(xs)
#print(ys)


plt.plot(xs, ys, marker='o', linestyle='none')

axes = plt.gca()
#axes.invert_yaxis()
ylabels = map(lambda t: '0x%08X' % int(t), axes.get_yticks())
axes.set_yticklabels(ylabels)

#plt.savefig('plot.svg')
plt.show()
