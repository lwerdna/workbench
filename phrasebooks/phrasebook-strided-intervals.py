#!/usr/bin/env python

import sys

# play with strided intervals, implementation taken from [0]

# 0: https://github.com/angr/claripy/blob/master/claripy/vsa/strided_interval.py
# 1: BinTrimmer: Towards Static Binary Debloating Through Abstract Interpretation

from claripy.vsa.strided_interval import *
from claripy.vsa.bool_result import BoolResult, TrueResult, MaybeResult, FalseResult

#def widen_custom(i0, i1):
#    if i0.is_integer and i1.is_integer

def dominates(a, b):
    return a.intersection(b).identical(b)

if __name__ == '__main__':
    # TEST:
    # has values {0}
    a = StridedInterval(None, 32, 1, 0, 0)
    # has values {0}
    b = StridedInterval(None, 32, 0x10000000, 0, 0)
    # has values:
    # [       '0x0', '0x10000000', '0x20000000', '0x30000000',
    #  '0x40000000', '0x50000000', '0x60000000', '0x70000000',
    #  '0x80000000', '0x90000000', '0xa0000000', '0xb0000000',
    #  '0xc0000000', '0xd0000000', '0xe0000000', '0xf0000000']
    c = StridedInterval(None, 32, 0x10000000, 0, 0xFFFFFFFF)
    breakpoint()

    # TEST:
    a = StridedInterval.min_int(32)         # -0x80000000
    b = StridedInterval.max_int(32)         # 0xffffffff
    c = StridedInterval.signed_max_int(32)  # 0x7fffffff
    d = StridedInterval.signed_min_int(32)  # -0x80000000
    breakpoint()

    # TEST: widen failure
    a = StridedInterval(None, 32, 1, 1000, 0xFFFFFFFF) # 0x000003E8 thru 0xFFFFFFFF
    b = StridedInterval(None, 32, 1, 1001, 0)          # 0x000003E9 thru 0x00000000
    c = a.widen(b)

    # TEST: TrueResult, FalseResult, MaybeResult
    a = StridedInterval(None, 32, 1, 0, 1000) # [0, 1000]
    b = StridedInterval(None, 32, 1, 500, 500) # 500
    c = StridedInterval(None, 32, 1, 1500, 1500) # 1500
    d = StridedInterval(None, 32, 1, 500, 1500) # [500, 1500]

    r0 = b.ULT(a) # 500 < [0, 1000] ..maybe
    assert BoolResult.is_maybe(r0)
    r1 = b.ULT(c) # 500 < 1500 ..
    assert BoolResult.is_true(r1)
    r2 = c.ULT(a) # 1500 < [0, 1000]
    assert BoolResult.is_false(r2)
    r3 = c.ULT(b) # 1500 < 500
    assert BoolResult.is_false(r3)
    r4 = d.ULT(a) # [500, 1500] < [0, 1000]
    assert BoolResult.is_maybe(r4)

    assert TrueResult and FalseResult == FalseResult
    assert TrueResult or FalseResult == TrueResult
    assert TrueResult and MaybeResult == MaybeResult
    assert TrueResult or MaybeResult == TrueResult
    assert FalseResult and MaybeResult == MaybeResult
    assert FalseResult or MaybeResult == MaybeResult

    breakpoint()

    # TEST: what is intersection of [0, 0x80000000] and [0x80000000, 0x3E8] ?
    a = StridedInterval(None, 32, 1, 0, 0x80000000)
    b = StridedInterval(None, 32, 1, 0x80000000, 0x3E8)
    c = a.intersection(b)

    # TEST: what is intersection of [0, 0x7FFFFFFFF] and [0x80000000, 0x3E8] ?
    a = StridedInterval(None, 32, 1, 0, 0x7FFFFFFF)
    b = StridedInterval(None, 32, 1, 0x80000000, 0x3E8)
    c = a.intersection(b)

    # TEST: what is the minimum 32-bit integer?
    a = StridedInterval.min_int(32)
    print(a)

    # TEST: a full range value (bottom) should interact with <0 to be all negative values, right?
    a = StridedInterval.top(bits=32)
    print(a)

     

    a = StridedInterval(None, 4, 2, 0b0100, 0b1100) # 4, 6, 8, 10, 12
    print(f'{a}: {a.eval(999)}')
    print('')

    for b in [
        StridedInterval(None, 4, 2, 0b1010, 0b1100), 
        StridedInterval(None, 4, 2, 0b1001, 0b1011),  # 9, 11
        StridedInterval(None, 4, 4, 0b1000, 0b1100) # 8, 12
    ]:
        print(f'{b}: {b.eval(999)}')

        b.normalize()
        print(f'b normalized: {b}')
        print(f'intersection is: {a.intersection(b)}')
        print(f'intersection is: {a.intersection(b)}')
        print(dominates(a,b))
        print('')
    sys.exit(0)

    # single values are constructed by setting lower_bound == upper_bound
    # stride value does not matter
    si = StridedInterval('singleton', 4, 1, 0b1010, 0b1010)
    print(f'{si}: {si.eval(999)}')
    si = StridedInterval('singleton', 4, 2, 0b1010, 0b1010)
    print(f'{si}: {si.eval(999)}')

    # simple test from 4.1 in [1]: a strided interval of 4-bit values from 0b1010 to 0b0010 with stride 2
    si = StridedInterval(None, 4, 2, 0b1010, 0b0010)

    # get at most 10 concrete values form the interval, should be:
    # { 0b1010, 0b1100, 0b1110, 0b0000, 0b0010 } = { 10, 12, 14, 0, 2 }
    print(si.eval(10))

    # if 0 is in the interval
    for x in range(16):
        print(f'Is {x} in the interval? {si.solution(x)}')

    # comparisons
    # signed      unsigned
    # SLT    <    ULT
    # SLE    <=   ULE
    # SGT    >    UGT
    # SGE    >=   UGE
    # is 15 greater than the interval? it should be
    print(f'15 > si == {si.ULT(15)}')
    print(f'14 > si == {si.ULT(14)}')
    print(f'13 > si == {si.ULT(13)}')

    si2 = StridedInterval(None, 4, 2, 0b1001)
    si3 = si.union(si2)
    #
    # si        si2
    # ------    ------
    #           0b1001
    # 0b1010
    #           0b1011
    # 0b1100
    #           0b1101
    # 0b1110
    #           0b1111
    # 0b0000
    #           0b0001
    # 0b0010
    print(si3.eval(999))
    # [9, 10, 11, 12, 13, 14, 15, 0, 1, 2]

    # <4>0x1[0x9, 0x2]

    def single(n, width=4):
        result = StridedInterval(None, width, 0, n, n)
        #result = StridedInterval(None, width, 1, n, n)
        #result = StridedInterval(None, width, 2**n, n, n)
        assert result.is_integer
        return result

    def single_widen(a, b, width=4):
        descr = f'{a} widened with {b}'
        result = set(single(a).widen(single(b)).eval(999999))
        print(f'{descr}: {result}')
        #result = set(single(a).widen(single(b)).eval(999999, True))
        #print(f'{" "*len(descr)}: {result}')
        return result

    single_widen(0, 1)
    single_widen(0, 2)
    single_widen(1, 1)
    single_widen(1, 2)
    single_widen(1, 3)
    single_widen(10, 11)
    single_widen(10, 12)

    # {6} widened with {8} will be {6,7,...,15}
    assert single_widen(6, 8) == {6,7,8,9,10,11,12,13,14,15}
    # {6} unioned {8} results in <4>2[6,8] ... it detects the stride and efficiently stores
    assert single(6).union(single(8)).eval(999) == [6,8]
    # {6,8} widened with {10} will be {6,8,10,12,14}
    assert single(6).union(single(8)).widen(single(10)).eval(999) == [6, 8, 10, 12, 14]
    # {6,8} widened with {2}
    result = single(6).union(single(8))
    print(result)
    result2 = result.widen(single(2))
    print(result2)

    sys.exit(0)
    def whats_lower_do(n, stride, bits=4):
        result = StridedInterval.lower(bits, n, stride)
        print(f'lower({n}, stride={stride}) = {result}')
        print('  from ' + str(StridedInterval(None, bits, 1, n, n).eval(999999)))

    whats_lower_do(10, 1, 4)

    #si = StridedInterval(

