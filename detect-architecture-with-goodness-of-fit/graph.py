#!/usr/bin/env python

import references

import matplotlib.pyplot as plt

def normalize(data):
    data[0] = 0
    s = sum(data)
    return [x/s for x in data]

x = list(range(256))

plt.title('x86_64')
plt.bar(x, normalize(references.counts_x86_64))
plt.savefig('reference_x86_64.png')
plt.clf()

plt.title('mips32')
plt.bar(x, normalize(references.counts_mips32))
plt.savefig('reference_mips32.png')
plt.clf()

plt.title('armv7')
plt.bar(x, normalize(references.counts_armv7))
plt.savefig('reference_armv7.png')
plt.clf()

plt.title('ppc')
plt.bar(x, normalize(references.counts_ppc))
plt.savefig('reference_ppc.png')
plt.clf()

