#!/usr/bin/env python

import os, sys, re, pprint

def process(line):
    first = None
    last = None
    for i in range(len(line)):
        value = None

        c = line[i]
        if c in '0123456789':
            value = int(c)
        elif line[i:].startswith('one'):
            value = 1
        elif line[i:].startswith('two'):
            value = 2
        elif line[i:].startswith('three'):
            value = 3
        elif line[i:].startswith('four'):
            value = 4
        elif line[i:].startswith('five'):
            value = 5
        elif line[i:].startswith('six'):
            value = 6
        elif line[i:].startswith('seven'):
            value = 7
        elif line[i:].startswith('eight'):
            value = 8
        elif line[i:].startswith('nine'):
            value = 9
        
        if value != None:
            if first == None:
                first = value
            last = value

    return 10*first + last

with open('input.txt') as fp:
    total = 0
    for line in fp.readlines():
        t = process(line)
        print(line.rstrip() + ': ' + str(t))
        total += t

    print('')
    print('total: ' + str(total))
