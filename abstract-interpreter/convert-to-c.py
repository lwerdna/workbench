#!/usr/bin/env python

# convert pseudocode used in AI development to C
# example invocation:
# $ ./pcode-codegen.py ./test-cases.py
#   (c code on stdout)

import sys
import ast

from helpers import *

def get_vars(tree):
    if type(tree) == list:
        return sum([get_vars(e) for e in tree], [])
    elif type(tree) == ast.Module:
        return get_vars(tree.body)
    elif type(tree) == ast.Expr:
        return get_vars(tree.value)
    elif type(tree) == ast.Call:
        return []
    elif type(tree) == ast.Constant:
        return []
    elif type(tree) == ast.Assign:
        return get_vars(tree.targets[0]) + get_vars(tree.value)
    elif type(tree) == ast.Name:
        return [tree.id]
    elif type(tree) == ast.BinOp:
        return get_vars(tree.left) + get_vars(tree.right)
    elif type(tree) == ast.If:
        return get_vars(tree.test) + get_vars(tree.body) + (get_vars(tree.orelse) if tree.orelse else [])
    elif type(tree) == ast.While:
        return get_vars(tree.test) + get_vars(tree.body)
    elif type(tree) == ast.BoolOp:
        return get_vars(tree.values[0]) + get_vars(tree.values[1])
    elif type(tree) == ast.Compare:
        return get_vars(tree.left) + get_vars(tree.comparators[0])
    else:
        breakpoint()

def codegen(tree, depth=0):
    indent = '\t'*depth
    if type(tree) == list:
        code = []
        for e in tree:
            code.extend(codegen(e, depth))
        return code
    elif type(tree) == ast.Module:
        return codegen(tree.body, depth)
    elif type(tree) == ast.Expr:
        return codegen(tree.value, depth)
    elif type(tree) == ast.Call:
        nargs = {'input':0}
        func_name = tree.func.id
        assert func_name in nargs, breakpoint()
        assert len(tree.args) == nargs[func_name]
        return ['input()']
    elif type(tree) == ast.Constant:
        if tree.value < 100:
            return [str(tree.value)]
        else:
            return [hex(tree.value)]
    elif type(tree) == ast.Assign:
        assert len(tree.targets) == 1
        lhs = codegen(tree.targets[0], depth)
        rhs = codegen(tree.value)
        assert len(lhs) == len(rhs) == 1, breakpoint()
        return [indent + lhs[0] + ' = ' + rhs[0] + ';']
    elif type(tree) == ast.Name:
        return [tree.id]
    elif type(tree) == ast.BinOp:
        op_str = None
        match type(tree.op):
            case ast.Sub:
                op_str = '-'
            case ast.Add:
                op_str = '+'
            case ast.Mult:
                op_str = '*'
        assert op_str
        lhs = codegen(tree.left, depth)
        rhs = codegen(tree.right)
        assert len(lhs) == len(rhs) == 1, breakpoint()
        return [indent + lhs[0] + op_str + rhs[0]]
    elif type(tree) == ast.If:
        cond = codegen(tree.test, depth)
        assert len(cond) == 1
        code = []
        code.append(f'{indent}if({cond[0]})')
        code.append(f'{indent}' + '{')
        code.extend(codegen(tree.body, depth+1))
        code.append(f'{indent}' + '}')
        if tree.orelse:
            code.append(f'{indent}else')
            code.append(f'{indent}' + '{')
            code.extend(codegen(tree.orelse, depth+1))
            code.append(f'{indent}' + '}')
        return code

    elif type(tree) == ast.While:
        test_true = codegen(tree.test, depth)
        cond = codegen(tree.test, depth)
        assert len(cond) == 1
        code = []
        code.append(f'{indent}while({cond[0]})')
        code.append(f'{indent}' + '{')
        code.extend(codegen(tree.body, depth+1))
        code.append(f'{indent}' + '}')
        return code

    elif type(tree) == ast.BoolOp:
        sym = { ast.Or: '||', ast.And: '&&' }[type(tree.op)]
        lhs = codegen(tree.values[0], depth)
        rhs = codegen(tree.values[1])
        assert len(lhs) == len(rhs) == 1, breakpoint()
        return [lhs[0] + sym + rhs[0]]

    elif type(tree) == ast.Compare:
        assert len(tree.ops) == 1
        assert len(tree.comparators) == 1
        sym = { ast.Eq: '==', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=' }[type(tree.ops[0])]
        lhs = codegen(tree.left, depth)
        rhs = codegen(tree.comparators[0])
        assert len(lhs) == len(rhs) == 1
        return [lhs[0] + sym + rhs[0]]

    else:
        breakpoint()

if __name__ == '__main__':
    fpath = './test-cases.py'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    print('#include <stdio.h>')
    print('#include <stdint.h>')

    print('uint32_t input(void) { return 999; }')

    with open(fpath) as fp:
        lines = fp.readlines()

    func_names = []
    starts = [i for i in range(len(lines)) if lines[i].startswith('# TEST:')]
    ends = starts[1:] + [len(lines)]
    assert len(starts) == len(ends)
    for (s,e) in zip(starts, ends):
        pycode_lines = lines[s+1: e]
        print('//' + '-'*78)
        print('//' + lines[s].rstrip())
        print('//' + '-'*78)
        func_name = f'test_{s}'
        func_names.append(func_name)
        print(f'void {func_name}(void)')
        print('{')
        tree = parse(''.join(pycode_lines))

        for vname in set(get_vars(tree)):
            print(f'\tuint32_t {vname};')

        code_lines = codegen(tree, 1)
        print('\n'.join(code_lines))
        print('}')
        print('')
    
    print('int main(int ac, char **av)')
    print('{')
    for fname in func_names:
        print(f'\t{fname}();')
    print('}')
