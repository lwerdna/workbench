#!/usr/bin/env python

# parse and display the AST of a given python source file

import os, sys

from helpers import *

if __name__ == '__main__':
    with open(sys.argv[1], "r") as fp:
        source = fp.read()

        tree = parse(source)
        print('-------- PYTHON AST --------')
        print(ast.dump(tree, indent=4))

        tree2 = refine(tree)
        print('-------- REFINED AST --------')
        pprint(tree2, indent=4)

