#!/usr/bin/env python

import os, sys

import entropy

data = list(open(sys.argv[1], 'rb').read())

print(entropy.entropy_A(data))

breakpoint()
