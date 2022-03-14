#!/usr/bin/env python

import os, sys, re, pprint

import pycparser

if __name__ == '__main__':
    filename = None
    if len(sys.argv) > 1:
        filename  = sys.argv[1]
    else:
        filename = 'test.h'

    ast = pycparser.parse_file(filename, use_cpp=True, cpp_path='gcc', cpp_args=['-E', r'-Iutils/fake_libc_include'])
    ast.show()
