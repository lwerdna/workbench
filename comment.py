#!/usr/bin/env python

import sys

fpath = sys.argv[1]
comment_str = sys.argv[2]

with open(fpath) as fp:
    lines = fp.readlines()

uncommented = bool([l for l in lines if not (l.startswith(comment_str))])

if uncommented:
    lines = [comment_str + l for l in lines]
    with open(fpath, 'w') as fp:
        fp.write(''.join(lines))
else:
    print('file %s already commented with "%s"' % (fpath, comment_str))
