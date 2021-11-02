#!/usr/bin/env python

import sys

fpath = sys.argv[1]
comment_str = sys.argv[2]

with open(fpath) as fp:
    lines = fp.readlines()

# every line starts with comment string <-> commented
commented = len([l for l in lines if l.startswith(comment_str)]) == len(lines)

if commented:
    lines = [l.replace(comment_str, '', 1) for l in lines]
    with open(fpath, 'w') as fp:
        fp.write(''.join(lines))
else:
    print('file %s is not commented with "%s"' % (fpath, comment_str))
