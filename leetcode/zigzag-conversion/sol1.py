#!/usr/bin/env python3

from collections import Counter

class Solution:
    def compute(self, s, numRows):
        if numRows <= 0: return ''
        if numRows == 1: return s
        
        result = [[] for x in range(numRows)]
        
        addend = 1
        dstidx = 0
        srcidx = 0
        
        while srcidx < len(s):
            print('srcidx:%d dstidx:%d' % (srcidx, dstidx))
            result[dstidx].append(s[srcidx])
            
            dstidx += addend
            if dstidx==0 or dstidx==numRows-1:
                addend = -addend

            srcidx += 1
            
        return ''.join(list(map(lambda x: ''.join(x), result)))

sol = Solution()

#assert(sol.compute('')==0)
#assert(sol.compute('z')==1)
#assert(sol.compute('au')==2)
#assert(sol.compute('abcabcbb')==3)
#assert(sol.compute('abba')==2)

print(sol.compute('abcdefg', 1))

assert(sol.compute('aasdfasdf', 0) == '')
assert(sol.compute('', 3) == '')
assert(sol.compute('a', 1) == 'a')
assert(sol.compute('a', 2) == 'a')
assert(sol.compute('a', 22) == 'a')
assert(sol.compute('abcd', 3) == 'abdc')
assert(sol.compute('PAYPALISHIRING', 3) == 'PAHNAPLSIIGYIR')
assert(sol.compute('PAYPALISHIRING', 4) == 'PINALSIGYAHRPI')



print('OK!')
