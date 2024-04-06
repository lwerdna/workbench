#!/usr/bin/env python

import os
import sys

import kconfiglib

class CustomExpression():
    def __init__(self, operator, operands):
        self.operator = operator
        self.operands = operands

operator2str = {
    kconfiglib.AND: 'and ',
    kconfiglib.OR: 'or ',
    kconfiglib.NOT: 'not ',
    kconfiglib.EQUAL: '== ',
    kconfiglib.UNEQUAL: '!= ',
    kconfiglib.LESS: '< ',
    kconfiglib.LESS_EQUAL: '<= ',
    kconfiglib.GREATER: '> ',
    kconfiglib.GREATER_EQUAL: '>= '
}

# is an expression "y"? <symbol y, bool, value y, constant>
def is_const_symbol(expr):
    return type(expr) == kconfiglib.Symbol and expr.is_constant

def is_y(expr):
    return is_const_symbol(expr) and expr.type == kconfiglib.BOOL and expr.name == 'y'

def is_n(expr):
    return is_const_symbol(expr) and expr.type == kconfiglib.BOOL and expr.name == 'n'

def expr_to_smt2(expr):
    if type(expr) == kconfiglib.Symbol:
        if is_y(expr):
            return 'true'
        return expr.name
    elif type(expr) == tuple:
        operator = expr[0]
        if not operator in operator2str:
            breakpoint()
        operands = expr[1:]
        return '(' + operator2str[operator] + ' '.join(expr_to_smt2(o) for o in operands) + ')'
    elif type(expr) == kconfiglib.Choice:
        return 'EXACTLY_ONE(' + ', '.join(expr_to_smt2(x) for x in expr.syms) + ')'
    elif type(expr) == CustomExpression:
        return '(' + expr.operator.join([expr_to_smt2(x) for x in expr.operands]) + ')'
    else:
        breakpoint()

    breakpoint()

def assert_expression(expr):
    return '(assert (' + expr_to_smt2(expr) + '))'

def assert_implies(left, right):
    return assert_expression(CustomExpression(' => ', [left, right]))

def collect_menu_nodes(node):
    result = []
    result.append(node)
    if node.list:
        if type(node.list) == list:
            for child in node.list:
                result.extend(collect_menu_nodes(child))
        else:
            result.extend(collect_menu_nodes(node.list))
    if node.next:
        result.extend(collect_menu_nodes(node.next))
    return result

def find_menu_node_by_sym_name_bfs(root, name):
    if root.item.__class__ is kconfiglib.Symbol:
        if root.item.name == name:
            return root

    for target in [root.next, root.list]:
        if not target:
            continue
        if subresult := find_menu_node_by_sym_name_bfs(target, name):
            return subresult

    return None

def menu_node_to_str_brief(node):
    if node.item.__class__ is kconfiglib.Symbol:
        return f'MENU (symbol:{node.item.name})'

    if node.item.__class__ is kconfiglib.Choice:
        s = "MENU (choice"
        if node.item.name is not None:
            s += " " + node.item.name
        s += ')'
        return s

    if node.item is kconfiglib.MENU:
        return "MENU (menu)"

    return "MENU (comment)"

# kconfiglib is configured through the environment
os.environ['srctree'] = '/home/andrewl/Downloads/linux-3.10.1'
os.environ['SRCARCH'] = 'arm'

kconf = kconfiglib.standard_kconfig()

#menu_nodes = collect_menu_nodes(kconf.top_node)
mnode_arm = find_menu_node_by_sym_name_bfs(kconf.top_node, 'ARM')
mnodes = collect_menu_nodes(mnode_arm)

print('digraph g {')
print(f'\t// {len(mnodes)} nodes')
for node in mnodes:
    label = menu_node_to_str_brief(node)
    print(f'\t{id(node)} [label="{label}"]')
print('\t// edges')
for node in mnodes:
    if node.list:
        print(f'\t{id(node)} -> {id(node.list)} [label="child"]')
    #if node.next:
    #    print(f'\t{id(node)} -> {id(node.next)} [label="next"]')
print('}')

