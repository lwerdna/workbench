import ast
from pprint import pprint

def refine(tree):
    if type(tree) == list:
        all([type(e)==ast.Expr for e in tree])
        return ['block'] + [refine(e) for e in tree]
    elif type(tree) == ast.Module:
        return refine(tree.body)
    elif type(tree) == ast.Expr:
        assert type(tree.value) == ast.Call
        return refine(tree.value)
    elif type(tree) == ast.Call:
        nargs = {'init':4, 'translation':2, 'rotation':3}
        fname = tree.func.id
        assert fname in nargs, breakpoint()
        assert len(tree.args) == nargs[fname]
        return [fname] + [refine(arg) for arg in tree.args]
    elif type(tree) == ast.Constant:
        return tree.value
    elif type(tree) == ast.While:
        assert tree.test.id == 'unknown'
        return ['iter', ['block'] + [refine(e) for e in tree.body]]
    elif type(tree) == ast.If:
        assert tree.test.id == 'unknown'
        return ['or', refine(tree.body), refine(tree.orelse)]
    else:
        breakpoint()

def parse(source):
    return ast.parse(source)
