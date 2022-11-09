#!/usr/bin/env python

# parse input string into an Expression Node object which has functions to get
# variable names and evaluate the expression based on input values

import ast

#------------------------------------------------------------------------------
# expression tree, nodes
#   And, Or, Not, Variable, Literal
#------------------------------------------------------------------------------

class ExprNode(object):
    @classmethod
    def true(self):
        return ValNode(True)
    @classmethod
    def false(self):
        return ValNode(False)

    def varnames(self):
        result = set()
        for c in self.children:
            result = result.union(c.varnames())
        return result

class AndNode(ExprNode):
    def __init__(self, children):
        self.children = children

    def evaluate(self, values):
        return all(c.evaluate(values) for c in self.children)

    def prune_vals(self):
        tmp = [c.prune_vals() for c in self.children]

        # if there's a single false being anded, return false
        if [c for c in tmp if c == False]:
            return ExprNode.false()

        # collect children that aren't true
        tmp = [c for c in tmp if c != True]
        match len(tmp):
            case 0:
                return ExprNode.false()
            case 1:
                return tmp[0]
            case _:
                return AndNode(tmp)

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)
        return type(other) == AndNode and self.children == other.children

    def __str__(self):
        return '(' + ' and '.join(str(c) for c in self.children) + ')'

class OrNode(ExprNode):
    def __init__(self, children):
        self.children = children

    def evaluate(self, values):
        return any(c.evaluate(values) for c in self.children)

    def prune_vals(self):
        tmp = [c.prune_vals() for c in self.children]

        # if there's a single true being or'd, return true
        if [c for c in tmp if c == True]:
            return ExprNode.true()

        # collect children that aren't false
        tmp = [c for c in tmp if c != False]
        match len(tmp):
            case 0:
                return ExprNode.false()
            case 1:
                return tmp[0]
            case _:
                return OrNode(tmp)

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == OrNode and self.children == other.children

    def __str__(self):
        return '(' + ' or '.join(str(c) for c in self.children) + ')'

class NotNode(ExprNode):
    def __init__(self, child):
        self.child = child

    def evaluate(self, values):
        return not self.child.evaluate(values)

    def prune_vals(self):
        tmp = self.child.prune_vals()
        if type(tmp) == ValNode:
            return ValNode(not tmp.value)
        return NotNode(tmp)

    def varnames(self):
        return self.child.varnames()

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == NotNode and self.child == other.child

    def __str__(self):
        return f'(not {self.child})'

class VarNode(ExprNode):
    def __init__(self, name):
        self.name = name

    def varnames(self):
        return {self.name}

    def prune_vals(self):
        return VarNode(self.name)

    def evaluate(self, values):
        return values[self.name]

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == VarNode and self.name == other.name

    def __str__(self):
        return self.name

class ValNode(ExprNode):
    def __init__(self, value):
        self.value = value

    def evaluate(self, values):
        return self.value

    def prune_vals(self):
        return ValNode(self.value)

    def __eq__(self, other):
        if type(other) == bool:
            other = ValNode(other)
        elif type(other) == str:
            other = parse(other)

        return type(other) == ValNode and self.value == other.value

    def __str__(self):
        return str(self.value)

#------------------------------------------------------------------------------
# parsing
#------------------------------------------------------------------------------

# refine the AST from parse()/ast.parse() to ExprNode
def refine(tree):
    if type(tree) == ast.Module:
        return refine(tree.body)
    elif type(tree) == list: # block
        assert len(tree) == 1
        return refine(tree[0])
    elif type(tree) == ast.Expr:
        return refine(tree.value)
    elif type(tree) == ast.UnaryOp:
        return NotNode(refine(tree.operand))
    elif type(tree) == ast.BoolOp:
        subr = [refine(v) for v in tree.values]
        if type(tree.op) == ast.Or:
            return OrNode(subr)
        elif type(tree.op) == ast.And:
            return AndNode(subr)
    elif type(tree) == ast.Name:
        return VarNode(tree.id)
    else:
        breakpoint()

# parse a logical expression in Python to ExprNode
def parse(input_):
    ast_tree = ast.parse(input_)
    expr_tree = refine(ast_tree)
    return expr_tree

#------------------------------------------------------------------------------
# test/main
#------------------------------------------------------------------------------

if __name__ == '__main__':
    expr = parse('A or (not A) and B')
    assert str(expr) == '(A or ((not A) and B))'
    assert expr.evaluate({'A':1, 'B':0}) == True
    assert expr.evaluate({'A':True, 'B':False}) == True
    vnames = list(expr.varnames())
    assert vnames == ['A', 'B'] or vnames == ['B', 'A']

    n = len(vnames)
    for i in range(2**n):
        inputs_ = {name: bool(i & (1<<(n-pos-1))) for (pos, name) in enumerate(vnames)}
        print(inputs_, '->', expr.evaluate(inputs_))

    tmp = ExprNode.true()
    assert tmp == ValNode(True)
    assert tmp == True

    tmp = ExprNode.false()
    assert tmp == ValNode(False)
    assert tmp == False

    # reduce A & True to A
    tmp = AndNode([VarNode('A'), ValNode(True)])
    print(tmp)
    tmp = tmp.prune_vals()
    assert str(tmp) == 'A'
    assert tmp == parse('A')
    assert tmp == parse('(A)')
    assert tmp == VarNode('A')
    print(tmp)

    print('pass')
