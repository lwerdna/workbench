#!/bin/bash

set -x # short for `set -o xtrace` see `man bash` for '-o option-name'

./method0 quiet
./method1 quiet
./method2.py quiet
./method3.py quiet
