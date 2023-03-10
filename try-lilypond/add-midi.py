#!/usr/bin/env python3

# add midi section

import os
import sys

if __name__ == '__main__':
    fpath = sys.argv[1]

    with open(fpath) as fp:
        contents = fp.read()

    i = len(contents)-1
    while contents[i].isspace():
        i -= 1

    if contents[i] != '}':
        raise Exception('input file does not end with \'}\'')

    print(contents[0:i-1])

    print('  \midi {')
    print('    \context {')
    print('      \Score')
    print('      tempoWholesPerMinute = #(ly:make-moment 72 4)')
    print('    }')
    print('  }')

    print('}')


