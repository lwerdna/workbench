#!/usr/bin/env python

import re
import ast

from interpreter import TreeNode, sasi_range, sasi_single, sasi_all, sasi_empty

#------------------------------------------------------------------------------
# Read precondition, postcondition from files
#------------------------------------------------------------------------------

# convert values in a [pre|post]condition to SASI from python native types like
# int, list of int
#
# example:
#         {'x':[a,b], 'y':[c,d], 'z':e}
#      to {'x':<32>1[a,b], 'y':<32>1[a,b], 'z':<32>0[e,e]}
def vals_to_sasis(cond):
    for vname in cond:
        if type(cond[vname]) == list:
            lo, hi = cond[vname]
            cond[vname] = sasi_range(lo, hi)
        elif type(cond[vname]) == int:
            lo = cond[vname]
            cond[vname] = sasi_single(lo)
        elif cond[vname] in ['anything', 'full', 'top']:
            cond[vname] = sasi_all()
        elif cond[vname] in ['nothing', 'empty', 'bottom']:
            cond[vname] = sasi_empty()
        else:
            breakpoint()
            pass

# parse lines in given source file for postconditions and preconditions
def parse_conditions(lines):
    precond, postcond = None, None
    for line in lines:
        if m := re.match(r'^# precondition: (.*)', line):
            precond = eval(m.group(1))
        if m := re.match(r'^# postcondition: (.*)', line):
            postcond = eval(m.group(1))

    if precond:
        vals_to_sasis(precond)
    if postcond:
        vals_to_sasis(postcond)

    assert precond != None and postcond != None

    return (precond, postcond)

#------------------------------------------------------------------------------
# Refine the AST from parse()/ast.parse() to TreeNode suitable for abstract
# interpretation
#------------------------------------------------------------------------------

def refine(tree, tree_node_class=TreeNode):
    if type(tree) == list:
        all([type(e)==ast.Expr for e in tree])
        return tree_node_class('block', None, *[refine(e, tree_node_class) for e in tree])
    elif type(tree) == ast.Module:
        return refine(tree.body, tree_node_class)
    elif type(tree) == ast.Expr:
        assert type(tree.value) == ast.Call
        return refine(tree.value, tree_node_class)
    elif type(tree) == ast.Call:
        nargs = {'init':4, 'translation':2, 'rotation':3, 'input':0}
        func_name = tree.func.id
        assert func_name in nargs, breakpoint()
        assert len(tree.args) == nargs[func_name]
        return tree_node_class('call', func_name, *[refine(arg, tree_node_class) for arg in tree.args])
    elif type(tree) == ast.Constant:
        return tree_node_class('const', tree.value)
    elif type(tree) == ast.Assign:
        assert len(tree.targets) == 1
        return tree_node_class('=', None, refine(tree.targets[0], tree_node_class), refine(tree.value, tree_node_class))
    elif type(tree) == ast.Name:
        return tree_node_class('name', tree.id)
    elif type(tree) == ast.BinOp:
        if type(tree.op) == ast.Sub:
            op_str = '-'
        elif type(tree.op) == ast.Add:
            op_str = '+'
        elif type(tree.op) == ast.Mult:
            op_str = '*'
        else:
            breakpoint()
        return tree_node_class(op_str, None, refine(tree.left, tree_node_class), refine(tree.right, tree_node_class))
    elif type(tree) == ast.If:
        test_true = refine(tree.test, tree_node_class)
        test_false = test_true.negate()
        children = [test_true, test_false, refine(tree.body, tree_node_class)]
        if tree.orelse:
            children.append(refine(tree.orelse, tree_node_class))
        else:
            children.append(tree_node_class('nop', None))
        return tree_node_class('if', None, *children)

    elif type(tree) == ast.Compare:
        assert len(tree.ops) == 1
        assert len(tree.comparators) == 1
        sym = { ast.Eq: '==', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=' }[type(tree.ops[0])]

        return tree_node_class(sym,
            None,
            refine(tree.left, tree_node_class),
            refine(tree.comparators[0], tree_node_class)
        )
    elif type(tree) == ast.While:
        test_true = refine(tree.test, tree_node_class)
        test_false = test_true.negate()
        return tree_node_class(
            'while',
            None,
            refine(tree.test),
            test_false,
            refine(tree.body),
            tree_node_class('nop', None)
        )
    elif type(tree) == ast.BoolOp:
        sym = { ast.Or: '||', ast.And: '&&' }[type(tree.op)]
        return tree_node_class(
            sym,
            None,
            refine(tree.values[0], tree_node_class),
            refine(tree.values[1], tree_node_class)
        )
    else:
        breakpoint()

def parse(source):
    return ast.parse(source)

if __name__ == '__main__':
    source = '''
x = 45
while x <= 100:
    if x >= 50:
        x = 45
    else:
        x = x + 1
'''

    tree = parse(source)
    print('-------- PYTHON AST --------')    
    print(ast.dump(tree, indent=4))    

    tree2 = refine(tree)
    print('-------- ABSTRACT INTERPRETER TREE --------')
    print(tree2)
