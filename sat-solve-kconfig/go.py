#!/usr/bin/env python

import os
import sys

import helpers
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

def expr_to_smt2(expr):
    if type(expr) == kconfiglib.Symbol:
        if helpers.is_y(expr):
            return 'true'
        return 'CONFIG_' + expr.name
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

# kconfiglib is configured through the environment
os.environ['srctree'] = '/home/andrewl/Downloads/linux-3.10.1'
os.environ['SRCARCH'] = 'arm'

kconf = kconfiglib.standard_kconfig()

for name, sym in kconf.syms.items():
    #if name == 'CRYPTO_DEV_NX_ENCRYPT':
    #    breakpoint()

    # name and type
    print(f'; CONFIG_{name} (type:{kconfiglib.TYPE_TO_STR[sym.orig_type]})')
    if sym.orig_type == kconfiglib.BOOL:
        print(f'(declare-fun CONFIG_{sym.name} () Bool)')
    #if sym.type != sym.orig_type:
    #    print(f'; type differs from selected type: {kconfiglib.TYPE_TO_STR[sym.type]}')

    # direct dependencies
    # A direct-depends on B means A wouldn't exist if not for B
    # or, A's existence logically implies B
    # so generate:
    # A -> B
    if sym.direct_dep:
        if not helpers.is_y(sym.direct_dep):
            print('; direct (not reverse) dependencies [DEPENDS ON]')
            print(assert_implies(sym, sym.direct_dep))

    # reverse dependencies
    # A reverse dependent on B means B depends on A, or A influence B
    # A -> B
    if sym.orig_selects:
        print('; reverse dependencies [SELECT]')
        # "select ARCH_HAS_TICK_BROADCAST if GENERIC_CLOCKEVENTS_BROADCAST"
        # becomes:
        # (ARCH_HAS_TICK_BROADCAST, GENERIC_CLOCKEVENTS_BROADCAST)
        #
        # "select ARCH_BINFMT_ELF_RANDOMIZE_PIE"
        # becomes:
        # (ARCH_BINFMT_ELF_RANDOMIZE_PIE, y)
        for (config_sym, conditional) in sym.orig_selects:
            antecedent = sym
            if not helpers.is_y(conditional):
                antecedent = (kconfiglib.AND, antecedent, conditional)
            consequent = config_sym
            print(assert_implies(antecedent, consequent))

    # weak reverse dependencies (RVD)
    # A RVD B means A influences B, but B can still be overridden
    if sym.orig_implies:
        print('; weak dependencies [IMPLIES]')
        for expr in sym.orig_implies:
            print('; ' + expr_to_smt2(sym.weak_rev_dep))

    #breakpoint()
    print('')
