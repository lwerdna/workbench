#!/usr/bin/env python

import os
import sys
import pickle
import base64

if __name__ == '__main__':
    objstr = sys.argv[1]

    print(f'decoding {objstr}')
    serialized = base64.b64decode(objstr)
    pickle.loads(serialized)

    print(f'done')
