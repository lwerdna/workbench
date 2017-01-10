#!/usr/bin/env python

import os
import sys
import pdb

###############################################################################
# TOKENIZING STUFF
###############################################################################

class TID:
	NUMLIT,ADD,SUB,MUL,DIV,LPAREN,RPAREN = range(7)

	@staticmethod
	def id2str(ident):
		lookup = {TID.NUMLIT:'NUMLIT', TID.ADD:'ADD', TID.DIV:'DIV', \
			TID.SUB:'SUB', TID.MUL:'MUL', TID.LPAREN:'LPAREN', 
			TID.RPAREN:'RPAREN'}
		if not ident in lookup:
			raise Exception("unknown token id: %d" % ident)
		return lookup[ident]
	
class Token:
	def __init__(self,ident,val=None):
		self.ident, self.val = ident, val

	def __str__(self):
		if self.ident == TID.NUMLIT:
			return 'NUMLIT"%d"' % self.val
		else:
			return TID.id2str(self.ident)

	def __eq__(self, rhs):
		result = None

		if rhs == None:
			result = False
		# can compare directly to ints
		elif type(rhs) == type(self.ident):
			result = rhs == self.ident
		# or to other tokens
		else:
			result = self.ident == rhs.ident and self.val == rhs.val

		return result

	def __ne__(self, rhs):
		return not self.__eq__(rhs)

class TokenManager:
	def __init__(self, tokenList):
		self.tokenList = tokenList
		self.i = 0

	def reset(self):
		self.i = 0

	def peek(self, nAhead=0):
		if (self.i + nAhead) >= len(self.tokenList):
			return None
		return self.tokenList[self.i + nAhead]
	
	def consume(self, expectTid=None):
		if self.isEnd():
			raise Exception("token list is empty")

		tok = self.tokenList[self.i]
		self.i += 1

		if expectTid != None and tok != expectTid:
			raise Exception("expected token %s but got instead %s" % (TID.id2str(expectTid), tok))
		
		return tok	

	def isEnd(self):
		return self.peek() == None

	def __str__(self):
		result = []
		for k in range(self.i, len(self.tokenList)):
			result.append("%d: %s" % (k, str(self.tokenList[k])))
		return "\n".join(result)

def tokenize(line):
	tokens = []
	line = line.rstrip()
	chars = list(line)

	i = 0
	while i < len(chars):
		c = chars[i]

		# '(' and ')'
		if c == '(':
			tokens.append(Token(TID.LPAREN))
			i += 1
		elif c == ')':
			tokens.append(Token(TID.RPAREN))
			i += 1
		# whitespace (skip)
		elif c.isspace():
			while i<len(chars) and chars[i].isspace():
				i += 1
		# numeric literals
		elif c.isdigit():
			value = ''
			while i<len(chars) and chars[i].isdigit():
				value += chars[i]
				i += 1
			tokens.append(Token(TID.NUMLIT, int(value)))
		# '+', '-', '*', '/'
		elif c == '+':
			tokens.append(Token(TID.ADD))
			i += 1
		elif c == '-':
			tokens.append(Token(TID.SUB))
			i += 1
		elif c == '*':
			tokens.append(Token(TID.MUL))
			i += 1
		elif c == '/':
			tokens.append(Token(TID.DIV))
			i += 1
		else:
			raise Exception("tokenizing on \"%s...\"" % chars[i:i+8])

	return TokenManager(tokens)

###############################################################################
# PARSING
###############################################################################

class Node:
	def __init__(self, name, children):
		self.name = name
		self.children = children

	def __str__(self):
		return '%s (%d children)' % (self.name, len(self.children))

	def printTree(self, depth=0):
		if(depth):
			print ' ' * 2*depth,
		print 'Node "%s"' % self.name

		for v in self.children:
			if isinstance(v, Node):
				v.printTree(depth+1)
			else:
				print ' ' * 2*(depth+1),
				print v

#------------------------------------------------------------------------------

#    E  -> A E_ 
def parse_E(mgr):
	l = parse_A(mgr)
	r = parse_E_(mgr)
	return Node('E', [l,r])

#    E_ -> '+' A E_
#       -> '-' A E_
#       -> <empty>
def parse_E_(mgr):
	tok = mgr.peek()

	if tok in [TID.ADD, TID.SUB]:
		mgr.consume()
		l = parse_A(mgr)
		r = parse_E_(mgr)
		return Node('E_', [str(tok), l, r])
	else:
		return None

#    A  -> F A_ 
def parse_A(mgr):
	l = parse_F(mgr)
	r = parse_A_(mgr)
	return Node('A', [l,r])

#    A_ -> '*' F A_
#       -> '/' F A_
#       -> <empty>
def parse_A_(mgr):
	tok = mgr.peek()
	if tok in [TID.MUL, TID.DIV]:
		mgr.consume()
		l = parse_F(mgr)
		r = parse_A_(mgr)
		return Node('A_', [str(tok), l, r])
	else:
		return None # produce empty string

#    F -> '(' E ')'
#      -> NUMLIT   
def parse_F(mgr):
	tok = mgr.peek()
	if tok == TID.LPAREN:
		mgr.consume()
		l = parse_E(mgr)
		mgr.consume(TID.RPAREN)
		return Node('F', [l])
	elif tok == TID.NUMLIT:
		mgr.consume()
		child = Node('NUMLIT', [int(tok.val)])
		return Node('F', [child])
	else:
		raise Exception("expected parenthesized expression or numeric " + \
			"but got instead: %s" % tok)

def parse(mgr):
	#pdb.set_trace()

	parseTree = parse_E(mgr)

	if not mgr.isEnd():
		raise Exception("expected end of input, got: %s" % mgr.peek())

	return parseTree

###############################################################################
# PARSE TREE -> ABSTRACT SYNTAX TREE
###############################################################################

def p2a_E(n):
	assert(n.name == 'E')
	A,E_ = n.children

	l = p2a_A(A)

	if E_ == None: # just pass thru, no add/sub
		return l
	else: 
		# build first node
		op = E_.children[0]
		r = p2a_A(E_.children[1])
		result = Node(op, [l, r])

		# build as we descend down E_'s
		cur = E_.children[2]
		while cur:
			assert(cur.name == 'E_')
			op = cur.children[0]
			result = Node(op, [result, p2a_A(cur.children[1])])
			cur = cur.children[2]

		return result

def p2a_A(n):
	if n.name != 'A':
		raise Exception("expected node 'A', got %s" % n.name)
	F,A_ = n.children

	l = p2a_F(F)

	if A_ == None: # just pass thru, no mul/div
		return l
	else: 
		# build first node
		op = A_.children[0]
		r = p2a_F(A_.children[1])
		result = Node(op, [l, r])

		# build as we descend down A_'s
		cur = A_.children[2]
		while cur:
			assert(cur.name == 'A_')
			op = cur.children[0]
			result = Node(op, [result, p2a_F(cur.children[1])])
			cur = cur.children[2]

		return result

def p2a_F(n):
	if not (n.name == 'F'):
		raise Exception("expected node 'F', got %s" % n.name)

	c0 = n.children[0]
	if c0.name == 'E':
		return p2a_E(c0)
	else:
		if not (c0.name == 'NUMLIT'):
			raise Exception("expected node 'NUMLIT', got %s" % c0.name)
		return c0 # should be NUMLIT

def parseTreeToAbstractSyntaxTree(n):
	assert(n.name == 'E')
	#pdb.set_trace()
	return p2a_E(n)

###############################################################################
# EVALUATE
###############################################################################

def evaluate(n):
	if n.name == 'NUMLIT':
		return n.children[0]

	c0,c1 = n.children
	if n.name == 'ADD':
		return evaluate(c0) + evaluate(c1)
	elif n.name == 'SUB':
		return evaluate(c0) - evaluate(c1)
	elif n.name == 'MUL':
		return evaluate(c0) * evaluate(c1)
	elif n.name == 'DIV':
		return evaluate(c0) / evaluate(c1)
	else:
		raise Exception("don't know how to evaluate '%s'" % n.name)

###############################################################################
# MAIN
###############################################################################

if __name__ == '__main__':
	for line in sys.stdin:
	#if 1:
		line = line.rstrip()
		#line = '(6+4)'

		print "input: " + line

		tokenMgr = tokenize(line)
		print 'tokens'
		print '------'
		print tokenMgr
		print ''

		parseTree = parse(tokenMgr)
		print 'parse tree'
		print '----------'
		print parseTree.printTree()
		print ''

		ast = parseTreeToAbstractSyntaxTree(parseTree)
		print 'abstract syntax tree'
		print '--------------------'
		print ast.printTree()
		print ''

		print "evaluated: %d" % evaluate(ast)
