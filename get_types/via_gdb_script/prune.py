#!/usr/bin/env python

import os, sys, re

from subprocess import Popen, PIPE

def list_text_files_current_dir():
    result = []
    for fname in os.listdir('.'):
        if re.match(r'.*\.txt$', fname):
            result.append(fname)
    return result

for path in list_text_files_current_dir():
    lines = []
    print('pruning %s' % path)
    with open(path) as fp:
        lines = [l.rstrip() for l in fp.readlines()]

    lines_new = []

    state = 'A'
    for line in lines:
        if state=='A':
            if line.startswith('All defined functions'):
                state='B'
        elif state=='B':
            if line.startswith('Non-debugging symbols'):
                break
            elif line.startswith('File '):
                pass
            elif line=='' or line.isspace():
                pass
            else:
                lines_new.append(line)

    with open(path, 'w') as fp:
        fp.write('\n'.join(lines_new))
