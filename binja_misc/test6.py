#!/usr/bin/env python

# do multiple binaries opened reference the same architecture instance?

import binaryninja

bv0 = binaryninja.open_view('/bin/ls')
assert bv0
bv1 = binaryninja.open_view('/bin/ln')
assert bv1
bv2 = binaryninja.open_view('/bin/cp')
assert bv2

print('binary views: %d %d %d' % (id(bv0), id(bv1), id(bv2)))

print('architectures: %d %d %d' % (id(bv0.arch), id(bv1.arch), id(bv2.arch)))

