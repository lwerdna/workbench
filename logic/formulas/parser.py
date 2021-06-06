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

class ASTNode():
    def __init__(self, left=None, right=None):
        self.left = left
        self.right = right

    def __eq__(self, other):
        return type(self) == type(other) and \
               (self.left == other.left) and \
               (self.right == other.right)

    def __eq_commutative__(self, other):
        return type(self) == type(other) and \
               ( ((self.left, self.right) == (other.left, other.right)) or
                 ((self.left, self.right) == (other.right, other.left)) )

class Conjunction(ASTNode):
    def __str__(self):
        return '(%s & %s)' % (str(self.left), str(self.right))

    def __eq__(self, other):
        return self.__eq_commutative__(other)

class Disjunction(ASTNode):
    def __str__(self):
        return '(%s | %s)' % (str(self.left), str(self.right))

    def __eq__(self, other):
        return self.__eq_commutative__(other)

class Implication(ASTNode):
    def __str__(self):
        return '(%s => %s)' % (str(self.left), str(self.right))

class BiImplication(ASTNode):
    def __str__(self):
        return '(%s <=> %s)' % (str(self.left), str(self.right))

    def __eq__(self, other):
        return self.__eq_commutative__(other)

class Negation(ASTNode):
    def __str__(self):
        return '~' + str(self.left)

class Contradiction(ASTNode):
    def __str__(self):
        return '_'

class Variable(ASTNode):
    def __str__(self):
        return self.left

class FormulasSemantics(object):
    def expression(self, ast):
        #print('expression: %s' % ast)

        if type(ast) == list:
            assert len(ast)==3
            assert ast[1] in ['&', '|', '=>', '<=>']

            if ast[1] == '&':
                return Conjunction(ast[0], ast[2])
            elif ast[1] == '|':
                return Disjunction(ast[0], ast[2])
            elif ast[1] == '=>':
                return Implication(ast[0], ast[2])
            elif ast[1] == '<=>':
                return BiImplication(ast[0], ast[2])
        else:
            # expression -> factor, pass through
            return ast

    def factor(self, ast):
        #print('factor: %s' % ast)

        if type(ast) == list:
            if len(ast) == 3:
                assert ast[0]=='(' and ast[2]==')'
                return ast[1]
            elif len(ast) == 2:
                assert ast[0]=='~'
                return Negation(ast[1])
            assert False
        else:
            # factor -> variable, pass through
            return ast

    def variable(self, ast):
        #print('variable: %s' % ast)

        assert len(ast) == 1
        return Variable(ast[0])
            
if __name__ == '__main__':
    ast = parse('~(A&B)=>(C |   ~D)=>E=>F')
    pprint.pprint(ast, width=20, indent=4)

    print(ast)
