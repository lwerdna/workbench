#!/bin/bash

set -x

cp ./test.bntl ~/repos/vector35/binaryninja/build_debug/out/binaryninja.app/Contents/Resources/typelib/mipsel32/libc.so.0.bntl
cp ./test.bntl ~/repos/vector35/binaryninja/build_release/out/binaryninja.app/Contents/Resources/typelib/mipsel32/libc.so.0.bntl
