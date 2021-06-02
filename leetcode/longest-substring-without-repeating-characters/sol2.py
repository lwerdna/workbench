#!/usr/bin/env python3
# this is a surprising one-pass solution I didn't come up with

from collections import Counter

class Solution:
    def compute(self, s):
        lookup = {}
        record = 0
        
        L = 0
        for R,char in enumerate(s):
            if char in lookup:
                L = max(lookup[char]+1, L)
            
            lookup[char] = R
            record = max(record, R-L+1)
            
        return record


sol = Solution()

#a = "abcabcbb" #abc
#a = 'bbbbb' #b
#a = 'pwwkew' #pwwkew
#a = "abcabcbb"
#a = 'au' # or 2
#a = '' # 0


assert(sol.compute('')==0)
assert(sol.compute('z')==1)
assert(sol.compute('au')==2)
assert(sol.compute('abcabcbb')==3)
assert(sol.compute('abba')==2)


ans = sol.compute('abcabcbb')

print(ans)
