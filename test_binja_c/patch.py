#!/usr/bin/env python
# patch binaryninjacore.h to be used by C compiler

import os, sys, re

fpath = os.path.join(os.environ['BN_API_PATH'], 'binaryninjacore.h')
with open(fpath) as fp:
    lines = [x.rstrip() for x in fp.readlines()]

i = 0
while i < len(lines):
    if '#include <cstdint>' in lines[i]: i+=1; continue
    if '#include <cstddef>' in lines[i]:  i+=1; continue
    if '#include <cstdlib>' in lines[i]:  i+=1; continue

    m = re.match(r'^(\s+)struct (.*);$', lines[i])
    if m:
        (space, name) = m.group(1,2)
        print('%stypedef struct %s %s;' % (space, name, name))
        i += 1
        continue

    m = re.match(r'^(\s+)(enum|struct) (.*?)( {)?$', lines[i])
    if m:
        (space, keyword, name, brack) = m.group(1,2,3,4)
        if not brack: brack=''
        print('%stypedef %s %s%s' % (space, keyword, name, brack))
        i += 1
        while lines[i] != '\t};':
            print(lines[i])
            i += 1
        print('\t} %s;' % name)
        i += 1
        continue

    print(lines[i])
    i += 1

