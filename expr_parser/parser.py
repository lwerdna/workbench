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
	def __init__(self, name):
		pass

	def printTree(self, depth=0):
		print ' ' * 2*depth,
		print 'Node "%s"' % self.name

#------------------------------------------------------------------------------

#    E  -> A E_ 
def parse_E(mgr):
	parse_A(mgr)
	parse_E_(mgr)
	if not mgr.isEnd():
		raise Exception("expected end of input, got: %s" % mgr.peek())

#    E_ -> '+' A E_
#       -> '-' A E_
#       -> <empty>
def parse_E_(mgr):
	tok = mgr.peek()
	if tok == TID.ADD:
		parse_A()
		parse_E_()
		# return add()
	if tok == TID.SUB:
		parse_A()
		parse_E_()
		# return sub()
	else:
		# empty

#    A  -> F A_ 
def parse_A(mgr):
	parse_F(mgr)
	parse_A_(mgr)
	# return something

#    A_ -> '*' F A_
#       -> '/' F A_
#       -> <empty>
def parse_A_(mgr):
	tok = mgr.peek()
	if tok == TID.ADD:
		mgr.consume(TID.ADD)
		parse_A()
		parse_E_()
		# return add()
	elif tok == TID.SUB:
		mgr.consume(TID.SUB)
		parse_A()
		parse_E_()
		# return sub()
	else
		# empty

#    F -> '(' E ')'
#      -> NUMLIT   
def parse_F(mgr):
	tok = mgr.peek()
	if tok == TID.LPAREN:
		mgr.consume(TID.LPAREN)
		parse_E()
		mgr.consume(TID.RPAREN)
		# return mul()
	elif tok == TID.NUMLIT:
		mgr.consume(TID.NUMLIT)
		return int(tok)
	else:
		raise Exception("expected parenthesized expression or numeric " + \
			"but got instead: %s" % tok)

###############################################################################
# MAIN
###############################################################################
if __name__ == '__main__':
	for line in sys.stdin:
		line = line.rstrip()

		print "input: " + line

		tokenMgr = tokenize(line)
		print 'tokens'
		print '------'
		print tokenMgr

		print ''

#		ast = parse(tokenMgr)
#		print 'parse tree'
#		print '----------'
#		print ast.printTree()
