#!/usr/bin/env python

import os
import sys

import ast
from pprint import pprint

def refine(tree):
    tt = type(tree)
    if tt == ast.BinOp:
        if type(tree.op) == ast.Sub:
            return ['-', refine(tree.left), refine(tree.right)]
        elif type(tree.op) == ast.Pow:
            return ['**', refine(tree.left), refine(tree.right)]            
    elif tt == ast.Module:
        return refine(tree.body)
    elif tt == list:
        assert len(tree) == 1
        return refine(tree[0])
    elif tt == ast.Expr:
        return refine(tree.value)
    elif tt == ast.Name:
        return ['var', tree.id]
    elif tt == ast.Constant:
        return ['const', tree.value]
    elif tt == ast.Call:
        if tree.func.value.id=='math' and tree.func.attr=='log':
            return ['log', refine(tree.args)]

    breakpoint()

def parse(source):
    return ast.parse(source)

def differentiate_tree(lnode, wrt='x'):
    op, A, B = lnode if lnode[2:] else lnode + [None]
    match lnode[0]:
        # sum rule, difference rule
        case '-'|'+':
            return [op, differentiate_tree(A), differentiate_tree(B)]
        # power rule
        case '**':
            if A == ['var', wrt] and B[0]=='const':
                e = B[1]
                return ['*', ['const', e], ['**', ['var', wrt], ['const', e-1]]]
        case 'log':
            if A == ['var', wrt]:
                return ['/', ['const', 1], ['var', wrt]]
    
    breakpoint()

def tree2str(lnode):
    op, A, B = lnode if lnode[2:] else lnode + [None]
    match lnode[0]:
        case '-'|'+'|'/'|'*'|'**':
            return f'({tree2str(A)} {op} {tree2str(B)})'
        case 'const'|'var':
            return str(A)

    breakpoint()


def tree2dot(lnode):
    def help0(lnode):
        if lnode[0] in ['const', 'var']:
            return [(id(lnode), str(lnode[1]))]
        return sum([help0(c) for c in lnode[1:]], [(id(lnode), str(lnode[0]))])

    def help1(lnode):
        result = []
        if lnode[0] in ['const', 'var']: return result
        for c in lnode[1:]:
            result.append((id(lnode), id(c)))
            result.extend(help1(c))
        return result

    print('digraph g {')
    print('\t// nodes')
    for (id_, label) in help0(lnode):
        print(f'\t{id_} [label="{label}"];')
    print('\t// edges')
    for (a, b) in help1(lnode):
        print(f'\t{a} -> {b};')
    print('}')
    
if __name__ == '__main__':
    source = 'x**2 - math.log(x)'
    if sys.argv[1:]:
        source = sys.argv[1]

    print(f'input: {source}')

    tree = parse(source)
    print('-------- PYTHON AST --------')
    print(ast.dump(tree, indent=4))

    tree2 = refine(tree)
    print('-------- REFINED AST --------')
    pprint(tree2, indent=4)

    #tree2dot(tree2)

    tree3 = differentiate_tree(tree2)
    print(tree3)

    result = tree2str(tree3)
    print(f'output: {result}')

    #tree2dot(tree3)

