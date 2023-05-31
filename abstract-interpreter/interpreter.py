#!/usr/bin/env python

import re
import ast
from operator import add
from functools import reduce
from pprint import pprint
from itertools import permutations
import math

from claripy.vsa.bool_result import BoolResult
from claripy.vsa.strided_interval import *

(RED, GREEN, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[0m')

#------------------------------------------------------------------------------
# operators for fixed-width integers
#------------------------------------------------------------------------------

def twos_compl(x, width=32):
    mask = 2**width - 1
    return ((x ^ mask) + 1) & mask

def reg_add(a, b, width=32):
    mask = 2**width - 1
    return (a + b) & mask

def reg_sub(a, b, width=32):
    mask = 2**width - 1
    return (a + twos_compl(b, width)) & mask

# We use C convention: 'int' is signed, 'unsigned int' isn't
# claripy uses convention: 'int' is unsigned, 'signed int' is

def max_int(width):
    # return StridedInterval.signed_max_int(32)
    return 2**(width-1) - 1

def max_uint(width):
    # return StridedInterval.max_int(32)
    return 2**(width) - 1

def min_int(width):
    #return StridedInterval.signed_min_int(32)
    return 2**(width-1)

def min_uint(width):
    #return StridedInterval.signed_min_int(32)
    return 0

# might help to think of these as the "lowest" (most counter clockwise)
# positions on the number circle
def max_xint(width):
    return max_uint(width)

def min_xint(width):
    return min_int(width)

#------------------------------------------------------------------------------
# signed-agnostic strided interval (SASI) helpers
#------------------------------------------------------------------------------

def circle_distance_clockwise(a, b, width=32):
    if a == 0:
        return b - a
    if b == 0:
        return (max_uint(width) + 1) - a
    if b >= a:
        return b - a
    return (max_uint(width) + 1) - (a - b)

def circle_wrap_needed(a, b, width=32):
    pass

# return a sasi representing a single value
def sasi_single(x, width=32):
    lo, hi = x, x
    return StridedInterval(None, width, 1, lo, hi)

# return a sasi representing all but single value
def sasi_all_but(x, width=32):
    lo, hi = reg_add(x, 1, width), reg_sub(x, 1, width)
    return StridedInterval(None, width, 1, lo, hi)

# return a sasi representing all possible values
def sasi_all(width=32):
    lo, hi = 0, 2**width-1
    return StridedInterval.top(width)

def sasi_empty(width=32):
    return StridedInterval(bits=width, bottom=True)

# return a sasi representing all possible values greater than or equal a given bound
def sasi_gte(bound, width=32, signed=None):
    match signed:
        case None:
            lo, hi = bound, max_xint(width)
        case True:
            lo, hi = bound, max_int(width)
        case False:
            lo, hi = bound, max_uint(width)
    result = StridedInterval(None, width, 1, lo, hi)
    return result

# return a sasi representing all possible values greater than a given bound
def sasi_gt(bound, width=32, signed=None):
    return sasi_gte(bound+1, width, signed)

# return a sasi representing all possible values less than or equal a given bound
def sasi_lte(bound, width=32, signed=None):
    match signed:
        case None:
            lo, hi = min_xint(width), bound
        case True:
            lo, hi = min_int(width), bound
        case False:
            lo, hi = min_uint(width), bound
    result = StridedInterval(None, width, 1, lo, hi)
    return result

# return a sasi representing all possible values less than a given bound
def sasi_lt(bound, width=32, signed=None):
    result = sasi_lte(bound-1, width, signed)
    return result

# return a sasi representing a range
def sasi_range(lo, hi, width=32):
    return StridedInterval(None, width, 1, lo, hi)

# does one SASI cover another?
def sasi_covers(a, b):
    return a.intersection(b).identical(b)
    # or, a.union(b).identical(b)

#def stride_widen_possibilities(x):
#    return {x//(2**i) for i in range(int(math.log(x)/math.log(2))+1) if i==0 or (x/(2**i)).is_integer()}

def stride_widen_possibilities(x):
    if x % 2:
        return {x, 1}
    return {x}.union(stride_widen_possibilities(x//2))

# DIY implementation of widen, being unhappy with claripy's
# https://github.com/angr/claripy/issues/289
def sasi_widen(a, b):
    if sasi_covers(a, b):
        return a

    assert a.bits == b.bits
    width = a.bits
    critical_points = {0, a.lower_bound, a.upper_bound, max_uint(width-1), max_uint(width-1)+1, max_uint(width)}
    critical_strides = stride_widen_possibilities(a.stride)

    candidates = [StridedInterval.top(width)]
    for lb in critical_points:
        for ub in critical_points:
            for stride in critical_strides:
                candidate = StridedInterval(None, width, stride, lb, ub)
                candidates.append(candidate)

    candidates = sorted(candidates, key=lambda i: i.cardinality)

    for c in candidates:
        if sasi_covers(c, a) and sasi_covers(c, b):
            return c

#------------------------------------------------------------------------------
# MISC
#------------------------------------------------------------------------------

# pretty-print strided interval
def sasi_str(si):
    if si.is_integer:
        #return str(si.lower_bound)
        return hex(si.lower_bound)
    elif si.is_bottom:
        return '(bottom)'
    elif si.stride == 1:
        mask = 1 << (si.bits - 1)
        # if msb is set, print in hex
        if (si.lower_bound & mask) or (si.upper_bound & mask):
            return f'[0x{si.lower_bound:X},0x{si.upper_bound:X}]'
        # else print in decimal
        return f'[{si.lower_bound},{si.upper_bound}]'
    else:
        # stride is funky, just print total sasi
        return str(si)

#------------------------------------------------------------------------------
# STATE UTILITIES
#------------------------------------------------------------------------------

def state_identical(x, y):
    if sorted(x.keys()) != sorted(y.keys()):
        return False

    for k in x.keys():
        if not x[k].identical(y[k]):
            return False

        #if str(x[k]) != str(y[k]):
        #    return False

    return True

# does left cover right?
def state_covers(left, right):
    for k in left.keys():
        if not (k in right and sasi_covers(left[k], right[k])):
            return False

    return True

# pretty-print state
# input: precondition like {'x':<sasi>, 'y':<sasi>}
def state_str(cond):
    if cond == None:
        return 'None'
    return '{' + ','.join((f'{k}:{sasi_str(v)}' for (k,v) in cond.items())) + '}'
    #return ', '.join((f'{k}:{sasi_str(v)}' for (k,v) in cond.items()))

def state_possible(state):
    return all([not val.is_bottom for val in state.values()])

#--------------------------------------------------------------------------
# state set operations
#--------------------------------------------------------------------------

#   takes: two states (dicts of variables and their SASI's)
# returns: a state where:
#          - variables in both states have their values unioned
#          - variables in only one state are replicated to the result
def abstr_union(a, b):
    result = {}

    if type(a)==list or type(b)==list:
        breakpoint()

    for varname in set(list(a.keys()) + list(b.keys())):
        if varname in a and varname in b:
            value = a[varname].union(b[varname])
        elif varname in a:
            value = a[varname]
        else:
            value = b[varname]

        result[varname] = value

    return result

def abstr_intersection(a, b):
    result = {}

    for varname in set(list(a.keys()) + list(b.keys())):
        if varname in a and varname in b:
            value = a[varname].intersection(b[varname])
        elif varname in a:
            value = a[varname]
        else:
            value = b[varname]

        result[varname] = value

    return result

# widens the variables in one state to the variables in another
def abstr_widen(a, b):
    result = {}

    for varname in set(list(a.keys()) + list(b.keys())):
        if varname in a and varname in b:
            #value = a[varname].widen(b[varname])
            value = sasi_widen(a[varname], b[varname])
        elif varname in a:
            value = a[varname]
        else:
            value = b[varname]

        result[varname] = value

    return result

#------------------------------------------------------------------------------
# TreeNode
#------------------------------------------------------------------------------

# TreeNode with:
#    labels for edges
class TreeNode(object):
    def __init__(self, ttype, data, *children):
        self.ttype = ttype
        self.children = list(children)

        # the data held by ttypes const, name, etc.
        self.data = data

        # abstract interpretation logging
        # these lists parallel the list of children
        self.log_pres = [] # the preconditions sent to children
        self.log_posts = [] # the postconditions returned from children

    #--------------------------------------------------------------------------
    # TreeNode utilities
    #--------------------------------------------------------------------------

    # copy (recursive)
    # make a copy of the tree rooted at this node
    # does NOT preserve logging
    def copy_re(self):
        assert type(self.ttype) == str
        assert type(self.data) in [str, int]
        return TreeNode(self.ttype, self.data, *[c.copy_re() for c in self.children])

    # return list of all nodes in subtree rooted at this node
    def nodes_re(self):
        return [self] + sum([c.nodes_re() for c in self.children], [])

    # return a set of variable names (with possible duplicates)
    def var_names(self):
        if self.ttype == 'name':
            return [self.data]
        return sum([c.var_names() for c in self.children], [])

    #--------------------------------------------------------------------------
    # TreeNode types convenience functions
    #--------------------------------------------------------------------------
    def is_numeric_expr(self):
        return self.ttype in ['const', 'name', '-', '+', '*', 'call']

    def is_numeric_comparison(self):
        return self.ttype in ['==', '!=', '>', '>=', '<', '<=']

    def is_boolean_valued(self):
        return self.is_numeric_comparison() or self.ttype in ['&&', '||', '==', '!=']

    def is_variable(self):
        return self.ttype == 'name'

    # return the children that are nodes (NOT primitive data types)
    def children_nodes(self):
        return [c for c in self.children if type(c) == TreeNode]

    #--------------------------------------------------------------------------
    # TreeNode abstract interpretation
    #--------------------------------------------------------------------------
    def AI(self, precond, bits=32):
        # initialize missing variables in state
        for vname in self.var_names():
            if not vname in precond:
                precond[vname] = StridedInterval.top(bits)

        # run abstract interpretation
        return self.AI_re(precond)

    def AI_re(self, precond):
        if self.is_numeric_expr():
            return self.eval_numeric(precond)

        if self.is_numeric_comparison():
            print('ERROR: expected logic to here to have flowed from if')
            breakpoint()

        if precond == None:
            return None

        # precondition is abstract store of state of machine, implemented as a dict, like:
        #   {x:<abstraction_of_x>, y:<abstraction_of_y>}
        # eg:
        #   {x:[20,32], y:[8,9]}

        if self.ttype == 'start':
            self.log_pres.append(state_str(precond))
            postcond = self.children[0].AI_re(precond)
            self.log_posts.append(state_str(postcond))

        elif self.ttype == 'nop':
            return precond

        # result of block with a,b,c,... is ...c(b(a(precond)))
        elif self.ttype == 'block':
            for c in self.children:
                self.log_pres.append(state_str(precond))
                postcond = c.AI_re(precond)
                self.log_posts.append(state_str(postcond))

                precond = postcond

            return postcond

        # conditional
        elif self.ttype == 'if':
            cond_t, cond_f, block_t, block_f = self.children

            self.log_pres.append(state_str(precond))
            state_t = cond_t.AI_boolean(precond)
            self.log_posts.append(f'{state_str(state_t)}')

            self.log_pres.append(state_str(precond))
            state_f = cond_f.AI_boolean(precond)
            self.log_posts.append(f'{state_str(state_f)}')

            # send the true state down the true block
            self.log_pres.append(state_str(state_t))
            postcond_t = block_t.AI_re(state_t)
            self.log_posts.append(state_str(postcond_t))

            # send the false state down the false block
            self.log_pres.append(state_str(state_f))
            postcond_f = block_f.AI_re(state_f)
            self.log_posts.append(state_str(postcond_f))

            # compute the postcondition
            st, sf = state_possible(state_t), state_possible(state_f)
            assert st or sf
            result = {}
            if st:
                assert state_possible(postcond_t)
                result = abstr_union(result, postcond_t)
            if sf:
                assert state_possible(postcond_f)
                result = abstr_union(result, postcond_f)

            return result

        # assignment
        elif self.ttype == '=':
            lhs, rhs = self.children
            assert lhs.ttype == 'name'
            assert rhs.is_numeric_expr()

            # get left hand side of comparison
            var_name = lhs.data
            self.log_pres.append(state_str(precond))
            lhs = lhs.eval_numeric(precond)
            self.log_posts.append(sasi_str(lhs))

            # get right hand side
            postcond = precond.copy() # dict copy
            self.log_pres.append(state_str(precond))
            var_value = rhs.AI_re(precond)
            self.log_posts.append(sasi_str(var_value))

            # postcondition is the precondition with the variable replaced
            postcond[var_name] = var_value
            return postcond

        # while is treated like if/else with fixed point iteration on the true block
        elif self.ttype == 'while':
            cond_t, cond_f, block_t, block_f = self.children

            self.log_pres.append(state_str(precond))
            state_t = cond_t.AI_boolean(precond)
            self.log_posts.append(f'{state_str(state_t)}')

            self.log_pres.append(state_str(precond))
            state_f = cond_f.AI_boolean(precond)
            self.log_posts.append(f'{state_str(state_f)}')

            # send the true state down the true block
            self.log_pres.append(state_str(state_t))
            postcond_t = block_t.AI_re(state_t)
            self.log_posts.append(state_str(postcond_t))

            # send the false state down the false block
            self.log_pres.append(state_str(state_f))
            postcond_f = block_f.AI_re(state_f)
            self.log_posts.append(state_str(postcond_f))

            # compute the postcondition
            st, sf = state_possible(state_t), state_possible(state_f)
            assert st or sf
            result = {}
            if sf:
                assert state_possible(postcond_f)
                result = abstr_union(result, postcond_f)

            # if it's impossible to enter the loop, return the postcond false
            if not st:
                return result

            #
            assert state_possible(postcond_t)
            result = abstr_union(result, postcond_t)

            converged = False

            x = postcond_t
            # iterate with union to see if convergence
            limit = 10
            print(f'// iterating while (union) with limit {limit}')
            for i in range(limit):
                print(f'// {i})  in: {x}')
                y = block_t.AI_re(x)
                print(f'//    out: {y}')
                if state_identical(x, y):
                    converged = True
                    break
                x = abstr_union(x, y)
                print(f'//  union: {x}')

            if converged:
                return y

            # widen to force convergence
            limit = 10
            print(f'// iterating while (widen) with limit {limit}')
            for i in range(limit):
                print(f'// {i})  in: {x}')
                y = block_t.AI_re(x)
                print(f'//    out: {y}')
                # do we already cover this output?
                if state_covers(x, y):
                    converged = True
                    break
                x = abstr_widen(x, y)
                print(f'//  widen: {x}')

            # return results
            assert converged
            result = abstr_union(result, x)
            return result

        else:
            print(f'unable to handle type {self.ttype}')
            breakpoint()

    def AI_boolean_basic(self, precond, sign_info={}):
        if self.is_numeric_comparison():
            return self.AI_numeric_comparison(precond, sign_info)

        self.log_pres.append(state_str(precond))
        postcond0 = self.children[0].AI_boolean_basic(precond, sign_info)
        self.log_posts.append(state_str(postcond0))

        self.log_pres.append(state_str(precond))
        postcond1 = self.children[1].AI_boolean_basic(precond, sign_info)
        self.log_posts.append(state_str(postcond1))

        if self.ttype == '||':
            return abstr_union(postcond0, postcond1)
        elif self.ttype == '&&':
            return abstr_intersection(postcond0, postcond1)

    def AI_boolean_enhanced(self, precond):
        # for each variable, guess the sign, apply abstract interpretation, then union all results
        vnames = set(self.var_names())
        def powerset(s):
            for i in range(len(s)+1):
                for c in itertools.combinations(s, i):
                    yield set(c)

        result = {}
        for s in powerset(vnames):
            sign_info = {vname:(vname in s) for vname in vnames}
            print(f'// evaluating boolean expression with sign info: {sign_info}')
            sub_result = self.AI_boolean_basic(precond, sign_info)
            result = abstr_union(result, sub_result)

        return result

    def AI_boolean(self, precond):
        assert self.is_boolean_valued()

        # determine if this should be evaluated 'basic' or 'enhanced'
        nodes = self.nodes_re()
        has_and = bool([n for n in nodes if n.ttype == '&&'])
        n_vars = len(set(self.var_names()))

        if has_and and n_vars < 4:
            # enhanced mode
            return self.AI_boolean_enhanced(precond)
        else:
            return self.AI_boolean_basic(precond)

    # INPUT:
    #   state precondition
    # OUTPUT:
    #   state postcondition, variable modified
    def AI_numeric_comparison(self, precond, sign_info={}):
        assert self.is_numeric_comparison()

        # currently only support '<var> <comparison> <numeric>' like 'x > 7'
        child0, child1 = self.children
        assert child0.is_variable() and child1.is_numeric_expr()
        varname = child0.data

        # get left hand side of comparison
        self.log_pres.append(state_str(precond))
        lhs = child0.eval_numeric(precond)
        self.log_posts.append(sasi_str(lhs))

        # get right hand side of comparison
        self.log_pres.append(state_str(precond))
        rhs = child1.eval_numeric(precond)
        assert rhs.is_integer
        rhs = rhs.lower_bound
        self.log_posts.append(hex(rhs))

        # intersect the current variable's SASI with a SASI that passes the comparison
        var_signed = sign_info.get(varname)

        match self.ttype:
            case '!=':
                mask = sasi_all_but(rhs)
            case '==':
                mask = sasi_single(rhs)
            case '>':
                mask = sasi_gt(rhs, 32, var_signed)
            case '>=':
                mask = sasi_gte(rhs, 32, var_signed)
            case '<':
                mask = sasi_lt(rhs, 32, var_signed)
            case '<=':
                #breakpoint()
                mask = sasi_lte(rhs, 32, var_signed)

        # return a new state with the variable's SASI replaced
        result = precond.copy() # dict copy
        result[varname] = precond[varname].intersection(mask)
        return result

    #--------------------------------------------------------------------------
    # TreeNode logical negation
    #--------------------------------------------------------------------------

    # logical negate (recursive)
    # returns a NEW tree representing the logical negation
    def negate_re(self):
        assert self.is_boolean_valued()
        c0, c1 = self.children

        if self.ttype in ['>', '>=', '<', '<=', '==', '!=']:
            ntype = {'>':'<=', '<=':'>', '<':'>=', '>=':'<', '==':'!=', '!=':'=='}[self.ttype]
            return TreeNode(ntype, None, c0.copy_re(), c1.copy_re())

        if self.ttype in ['&&', '||']: # De Morgan
            assert c0.is_boolean_valued() and c1.is_boolean_valued()
            ntype = {'&&':'||', '||':'&&'}[self.ttype]
            return TreeNode(ntype, None, c0.negate(), c1.negate())

        print('unable to negate node type {self.ttype}')
        breakpoint()

    def negate(self):
        assert self.is_boolean_valued()
        return self.negate_re()

    #--------------------------------------------------------------------------
    # TreeNode logical evaluation
    #--------------------------------------------------------------------------

    # INPUT:
    #   sign_info: a dictionary of varname to {True, False, None} (signed, unsigned, unsure)
    # OUTPUT:
    #   BoolResult (false, maybe, true)
    def evaluate_boolean(state, sign_info):
        assert self.is_boolean_valued()
        assert len(self.children) == 2
        c0, c1 = self.children

        if self.ttype == '&&':
            return c0.evaluate_boolean(state, sign_info) and c1.evaluate_boolean(state, sign_info)
        if self.ttype == '||':
            return c0.evaluate_boolean(state, sign_info) or c1.evaluate_boolean(state, sign_info)

        assert self.is_numeric_comparison()

        # we'll use signed bounds if every variable in this expression is marked signed
        # TODO: look deeper
        all_signed = all([sign_info.get(x) == True for x in self.var_names()])
        all_unsigned = all([sign_info.get(x) == False for x in self.var_names()])

        v0 = c0.eval_numeric(state)
        v1 = c1.eval_numeric(state)

        match self.ttype:
            case '!=':
                return c0 != c1
            case '==':
                return c0 == c1
            case '>':
                if all_signed: return v0.SGT(v1)
                if all_unsigned: return v0.UGT(v1)
                return v0.SGT(v1) or v0.UGT(v1)
            case '>=':
                if all_signed: return v0.SGE(v1)
                if all_unsigned: return v0.UGE(v1)
                return v0.SGE(v1) or v0.UGE(v1)
            case '<':
                if all_signed: return v0.SLT(v1)
                if all_unsigned: return v0.ULT(v1)
                return v0.SLT(v1) or v0.ULT(v1)
            case '<=':
                if all_signed: return v0.SLE(v1)
                if all_unsigned: return v0.ULE(v1)
                return v0.SLE(v1) or v0.ULE(v1)

    def eval_numeric(self, state):
        assert self.is_numeric_expr()

        if self.ttype == 'const':
            value = self.data
            return StridedInterval(None, 32, 1, value, value)

        elif self.ttype == 'name':
            var_name = self.data
            return state[var_name]

        elif self.ttype in ['-', '+', '*']:
            # log
            self.log_pres.append(state_str(state))
            a = self.children[0].eval_numeric(state)
            self.log_posts.append(sasi_str(a))

            self.log_pres.append(state_str(state))
            b = self.children[1].eval_numeric(state)
            self.log_posts.append(sasi_str(b))

            if self.ttype == '-':
                return a - b
            elif self.ttype == '+':
                return a + b
            elif self.ttype == '*':
                return a * b

        elif self.ttype == 'call':
            func_name = self.data
            if func_name == 'input':
                return StridedInterval.top(32)
            print(f'unable to handle function call {func_name}()')
            breakpoint()

        else:
            print(f'unable to handle node type {self.ttype}')
            breakpoint()

    #--------------------------------------------------------------------------
    # TreeNode string functions
    #--------------------------------------------------------------------------
    def __str_helper__(self, depth):
        indent = '  '*depth

        line0 = indent + self.str_short()

        #if entries := self.log_pres():
        #    line0 += f' {RED}{va}{NORMAL}'

        lines = [line0]
        for c in self.children:
            if type(c) == TreeNode:
                lines.extend(c.__str_helper__(depth+1))
            else:
                lines.append(indent + '  ' + str(c))
        return lines

    def __str__(self):
        return '\n'.join(self.__str_helper__(0))

    def str_short(self):
        return self.ttype + (f': {self.data}' if self.data != None else '')

if __name__ == '__main__':
    assert twos_compl(0) == 0
    assert twos_compl(1) == 0xFFFFFFFF
    assert twos_compl(2) == 0xFFFFFFFE

    assert reg_add(0, 0) == 0
    assert reg_add(0, 1) == 1
    assert reg_add(0xFFFFFFFF, 0) == 0xFFFFFFFF
    assert reg_add(0xFFFFFFFE, 1) == 0xFFFFFFFF
    assert reg_add(0xFFFFFFFF, 1) == 0

    assert reg_sub(0, 0) == 0
    assert reg_sub(0, 1) == 0xFFFFFFFF
    assert reg_sub(0, 2) == 0xFFFFFFFE
    assert reg_sub(0xFFFFFFFF, 0) == 0xFFFFFFFF
    assert reg_sub(0xFFFFFFFE, 1) == 0xFFFFFFFD
    assert reg_sub(0xFFFFFFFF, 1) == 0xFFFFFFFE

    x = sasi_single(7, 32)
    assert x.is_integer
    assert x.cardinality == 1

    x = sasi_all_but(7, 32)
    assert x.cardinality == 2**32 - 1
    assert str(sasi_all_but(7, 32)) == '<32>0x1[0x8, 0x6]'

    x = sasi_single(7, 32).complement
    assert x.cardinality == 2**32 - 1
    assert str(sasi_all_but(7, 32)) == '<32>0x1[0x8, 0x6]'

    x = StridedInterval(None, 32, 1, 0x1234, 0x56789ABC)
    assert x.cardinality == 0x56789ABC - 0x1234 + 1

    x = x.complement
    assert x.cardinality == 2**32 - (0x56789ABC - 0x1234 + 1)

    assert min_uint(16) == 0
    assert max_uint(16) == 0xFFFF
    assert min_int(16) == 0x8000
    assert max_int(16) == 0x7FFF
    assert min_uint(32) == 0
    assert max_uint(32) == 0xFFFFFFFF
    assert min_int(32) == 0x80000000
    assert max_int(32) == 0x7FFFFFFF

    assert max_xint(32) == 0xFFFFFFFF
    assert min_xint(32) == 0x80000000

    # UNSIGNED
    # unsigned x > 1000
    tmp = sasi_gt(1000, 32, False)
    assert str(tmp) == '<32>0x1[0x3e9, 0xffffffff]'
    # unsigned x >= 1000
    tmp = sasi_gte(1000, 32, False)
    assert str(tmp) == '<32>0x1[0x3e8, 0xffffffff]'
    # unsigned x < 1000
    tmp = sasi_lt(1000, 32, False)
    assert str(tmp) == '<32>0x1[0x0, 0x3e7]'
    # unsigned x <= 1000
    tmp = sasi_lte(1000, 32, False)
    assert str(tmp) == '<32>0x1[0x0, 0x3e8]'

    # SIGNED
    # signed x > 1000
    tmp = sasi_gt(1000, 32, True)
    assert str(tmp) == '<32>0x1[0x3e9, 0x7fffffff]'
    # signed x >= 1000
    tmp = sasi_gte(1000, 32, True)
    assert str(tmp) == '<32>0x1[0x3e8, 0x7fffffff]'
    # signed x < 1000
    tmp = sasi_lt(1000, 32, True)
    assert str(tmp) == '<32>0x1[0x80000000, 0x3e7]'
    # signed x <= 1000
    tmp = sasi_lte(1000, 32, True)
    assert str(tmp) == '<32>0x1[0x80000000, 0x3e8]'

    # UNKNOWN (AGNOSTIC)
    # x > 1000                                      # UNSIGNED results are the superset
    tmp = sasi_gt(1000, 32)
    assert str(tmp) == '<32>0x1[0x3e9, 0xffffffff]'
    # x >= 1000
    tmp = sasi_gte(1000, 32)
    assert str(tmp) == '<32>0x1[0x3e8, 0xffffffff]'
    # x < 1000                                      # SIGNED results are the superset
    tmp = sasi_lt(1000, 32)
    assert str(tmp) == '<32>0x1[0x80000000, 0x3e7]'
    # x <= 1000
    tmp = sasi_lte(1000, 32)
    assert str(tmp) == '<32>0x1[0x80000000, 0x3e8]'

    # circle distance
    assert circle_distance_clockwise(0, 0) == 0
    assert circle_distance_clockwise(0, 1) == 1
    assert circle_distance_clockwise(0, 2) == 2
    assert circle_distance_clockwise(0xFFFFFFFD, 0) == 3
    assert circle_distance_clockwise(0xFFFFFFFE, 0) == 2
    assert circle_distance_clockwise(0xFFFFFFFF, 0) == 1
    assert circle_distance_clockwise(10, 20) == 10
    assert circle_distance_clockwise(123456, 999999) == 876543
    assert circle_distance_clockwise(99999999, 3000000000) == 2900000001
    assert circle_distance_clockwise(20, 10) == 2**32 - 10
    assert circle_distance_clockwise(999999, 123456) == 2**32 - 876543
    assert circle_distance_clockwise(3000000000, 99999999) == 2**32 - 2900000001

    # stride widening
    assert stride_widen_possibilities(1) == {1}
    assert stride_widen_possibilities(2) == {2,1}
    assert stride_widen_possibilities(3) == {3,1}
    assert stride_widen_possibilities(4) == {4,2,1}
    assert stride_widen_possibilities(5) == {5,1}
    assert stride_widen_possibilities(6) == {6,3,1}
    assert stride_widen_possibilities(7) == {7,1}
    assert stride_widen_possibilities(8) == {8,4,2,1}
    assert stride_widen_possibilities(9) == {9,1}
    assert stride_widen_possibilities(10) == {10,5,1}
    assert stride_widen_possibilities(11) == {11,1}
    assert stride_widen_possibilities(12) == {12,6,3,1}
    assert stride_widen_possibilities(13) == {13,1}
    assert stride_widen_possibilities(14) == {14,7,1}
    assert stride_widen_possibilities(15) == {15,1}
    assert stride_widen_possibilities(16) == {16,8,4,2,1}

    print('PASS')
