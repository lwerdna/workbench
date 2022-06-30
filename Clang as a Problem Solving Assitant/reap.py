#!/usr/bin/env python

import re

with open('tests-O3.ll') as fp:
    curfunc = None
    for line in [l.strip() for l in fp.readlines()]:
        if m := re.match(r'^define.*@(.*)\(.*$', line):
            #print(f'found function: {m.group(1)}')
            curfunc = m.group(1)
        elif line == '}':
            curfunc = None
        elif re.match(r'^.*call void @print_impossible().*$', line):
            if curfunc != 'main':
                print(f'failed to optimize/simplify {curfunc}()')
