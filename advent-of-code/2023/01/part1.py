#!/usr/bin/env python

import os, sys, re, pprint

def process(line):
    first = None
    last = None
    for c in line:
        if c in '0123456789':
            if first == None:
                first = c
            last = c
    return int(first)*10 + int(last)

with open('input.txt') as fp:
    total = 0
    for line in fp.readlines():
        t = process(line)
        print(line.rstrip() + str(t))
        total += t

    print(total)
