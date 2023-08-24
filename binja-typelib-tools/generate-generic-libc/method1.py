#!/usr/bin/env python

# resources:
# https://github.com/eliben/pycparser/blob/master/examples/explore_ast.py

import os, sys, re, pprint

import pycparser

if __name__ == '__main__':
    filename = None
    if len(sys.argv) > 1:
        filename  = sys.argv[1]
    else:
        filename = 'prototypes.h'

    ast = pycparser.parse_file(filename)

    for external_declaration in ast.ext:
        if type(external_declaration) == pycparser.c_ast.Typedef:
            pass
        elif type(external_declaration) == pycparser.c_ast.Decl:
            # TODO
        breakpoint()
    ast.show()
