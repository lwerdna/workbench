#!/usr/bin/env python

import os, sys, re
import pathlib

import tatsu
import pprint

parser = None

def parse(expression):
    global parser

    # locate and load the grammar
    if not parser:
        fpath = os.path.join(pathlib.Path(__file__).parent.absolute(), 'formulas.ebnf')
        grammar = open(fpath).read()
        parser = tatsu.compile(grammar)

    #ast = parser.parse(expression)
    ast = parser.parse(expression, semantics=FormulasSemantics())

    return ast

# the "semantics" of the returned AST is a little dictionary
# holding the type and left/right side

class FormulasSemantics(object):
    def expression(self, ast):
        #print('expression: %s' % ast)

        # expression -> factor
        if type(ast) == dict:
            return ast

        assert len(ast)==3, str(ast)
        if ast[1] == '^':
            return {'type':'conjunction', 'left':ast[0], 'right':ast[2]}
        elif ast[1] == 'v':
            return {'type':'disjunction', 'left':ast[0], 'right':ast[2]}
        elif ast[1] == '->':
            return {'type':'implication', 'left':ast[0], 'right':ast[2]}
        assert False

    def factor(self, ast):
        #print('factor: %s' % ast)

        # factor -> variable
        if type(ast) == dict:
            return ast

        elif len(ast) == 3: # factor -> '(' expression ')'
            assert ast[0]=='(' and ast[2]==')'
            return ast[1]

        assert False

    def variable(self, ast):
        #print('variable: %s' % ast)

        assert len(ast) == 1
        return {'type':'variable', 'name':ast[0]}

def ast2str(ast):
    if ast['type'] == 'variable':
        return ast['name']
    if ast['type'] in ['conjunction', 'disjunction', 'implication']:
        oper = { 'conjunction':'^',
                 'disjunction':'v',
                 'implication':'->' }[ast['type']]
        return '(%s%s%s)' % (ast2str(ast['left']), oper, ast2str(ast['right']))
    assert False
            
if __name__ == '__main__':
    ast = parse('(A^B)->(C v   D)->E->F')
    pprint.pprint(ast, width=20, indent=4)

    print(ast2str(ast))
