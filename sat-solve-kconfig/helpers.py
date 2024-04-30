#!/usr/bin/env python

import os
import re

import kconfiglib

###############################################################################
# kernel, kconf
###############################################################################

def get_kernel_path():
    PATH_DOWNLOADS = os.path.join(os.environ['HOME'], 'Downloads')
    candidates = []
    candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-3.10'))
    #candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-3.10.1'))
    #candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-master'))
    for candidate in candidates:
        if os.path.exists(candidate):
            return candidate

def get_kconf_object(ARCH='arm', VERSION='3.10'):
    # kconfiglib is configured through the environment
    kernel_path = get_kernel_path()
    kernel_version = re.search(r'/linux-(.*)$', kernel_path).group(1)
    os.environ['srctree'] = kernel_path
    os.environ['ARCH'] = ARCH
    os.environ['SRCARCH'] = ARCH
    os.environ['KERNELVERSION'] = kernel_version
    kconf = kconfiglib.standard_kconfig()
    return kconf

###############################################################################
# dependency handling
###############################################################################

# return a map <sym_A> -> [<sym_0, cond_0>, <sym_1, cond_1>, ...>] where:
# sym_i is all the symbols that select sym_A
def create_select_map(kconf):
    result = {}
    for src in kconf.defined_syms:
        for (dst, cond) in src.orig_selects:
            if not dst.name in result:
                result[dst.name] = []
            result[dst.name].append((src, cond))
    return result

###############################################################################
# expression parsing/handling
###############################################################################

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

def expr_to_str(expr):
    if type(expr) == kconfiglib.Symbol:
        if is_y(expr):
            return 'true'
        return expr.name
    elif type(expr) == tuple:
        operator = expr[0]
        if not operator in operator2str:
            breakpoint()
        operands = expr[1:]
        return '(' + operator2str[operator] + ' '.join(expr_to_str(o) for o in operands) + ')'
    elif type(expr) == kconfiglib.Choice:
        return 'EXACTLY_ONE(' + ', '.join(expr_to_str(x) for x in expr.syms) + ')'
    elif type(expr) == CustomExpression:
        return '(' + expr.operator.join([expr_to_str(x) for x in expr.operands]) + ')'
    else:
        breakpoint()

    breakpoint()

###############################################################################
# test
###############################################################################

if __name__ == '__main__':
    print(f'kernel path: {get_kernel_path()}')
