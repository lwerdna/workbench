#!/usr/bin/env python

import os, sys, re, pprint

variables = 'abcdefghijklm'

for i in range(len(variables)-1):
    for j in range(i+1, len(variables)):
        x = variables[i]
        y = variables[j]

        print('\t\t(and (= %c %c) (distinct %s))' % (
            x, y,
            ' '.join(sorted(set(variables) - {x, y}))
        ))


