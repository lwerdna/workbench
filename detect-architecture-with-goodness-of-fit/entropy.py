#!/usr/bin/env python

import os
import sys
import math

import references

def calculate_entropy(blob, width):
    assert width%2 == 0
    assert width <= len(blob)

    result = []

    for i in range(len(blob)):
        left = i-width//2
        right = i+width//2

        if left < 0:
            shift = -left
            left, right = 0, right+shift
        elif right > len(blob):
            shift = len(blob)-right
            left, right = left-shift, len(blob)

        counts = [0]*256
        for b in blob[left:right]:
            counts[b] += 1

        s = sum(counts)
        entropy = 0
        for k in range(width):
            p = counts[k]/s
            if p > 0:
                entropy += p * math.log(p)/math.log(2)
        result.append(-entropy)

    return result

# produce a graph of the bytes of the file vs. the calculated entropy
if __name__ == '__main__':
    width = 32
    fpath = sys.argv[0]
    blob = open(sys.argv[1], 'rb').read()

    x = list(range(len(blob)))

    import matplotlib.pyplot as plt

    fig, (ax1, ax2) = plt.subplots(2, 1, layout='constrained')

    ax1.set_ylabel('byte')
    #ax1.bar(x, list(blob))
    ax1.plot(x, list(blob))

    entropy = calculate_entropy(blob, width)
    ax2.set_xlabel('offset')
    ax2.set_ylabel('entropy')
    ax2.plot(x, entropy, 'r-')

    #plt.savefig('/tmp/tmp.png')
    #plt.close(fig)
    plt.show()
