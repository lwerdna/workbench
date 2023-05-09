#!/usr/bin/env python
# https://esolangs.org/wiki/Thue

import os, sys, re, random

if len(sys.argv) < 2:
    raise Exception('usage: %s script.t' % sys.argv[1])
verbose = sys.argv[2:] and sys.argv[2] in ['-trace', '-debug', '-verbose', '-v']

rules = []
linenum = 0;
stage = 'readrules'
progstate = ''
with open(sys.argv[1]) as fp:
    while True:
        linenum += 1
        line = fp.readline()
        if line == '':
            break
        if line == '\n':
            continue
        line = line.rstrip()

        if stage == 'readrules':
            if re.match('^\s*::=\s*$', line):
                stage = 'readstring'
                continue
            idx = line.find('::=')
            if idx == -1:
                raise Exception('line %d: %s ERROR: missing ::=' % (linenum, line))
            before = line[0:idx]
            after = line[idx+3:]
            rules.append((before, after))
        elif stage == 'readstring':
            progstate += line

if verbose:
    print('read rules:')
    for (before, after) in rules:
        print('%s ::= %s' % (before, after))
    print('read initial state:')
    print(progstate)

#print('executing')
while True:
    random.shuffle(rules)

    for (before, after) in rules:

        if before in progstate:
            if after.startswith('~'):
                print(after[1:])
                after = ''
            elif after == ':::':
                after = input().rstrip()
            progstate = progstate.replace(before, after, 1)
            break
    else:
        break

    if verbose:
        print('new state:', progstate)

