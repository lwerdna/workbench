#!/usr/bin/env python3

from collections import Counter

class Solution:
    def compute(self, str):
        INT_MIN = -(2**31)
        INT_MAX = 2**31-1

        L = 0
        while L<len(str) and str[L]==' ':
            L += 1
        
        #
        if L >= len(str): return 0
        R = L+1 if str[L] in '+-' else L
        while R<len(str) and str[R].isdigit():
            R += 1
            
        if L >= R: return 0
        
        try:
            ans = int(str[L:R])
        except Exception:
            return 0
            
        if ans < 0: return max(ans, INT_MIN)
        return min(ans, INT_MAX)

sol = Solution()

print(sol.compute('   -42'))

assert(sol.compute('-5-') == -5)
assert(sol.compute('42') == 42)
assert(sol.compute('-') == 0)
assert(sol.compute('   -') == 0)
assert(sol.compute('-'    ) == 0)
assert(sol.compute('   -42') == -42)
assert(sol.compute('+') == 0)
assert(sol.compute('   +') == 0)
assert(sol.compute('+'    ) == 0)
assert(sol.compute('   +42') == 42)
assert(sol.compute('4193 with words') == 4193)
assert(sol.compute('words and 987') == 0)
assert(sol.compute('-91283472332') == -2147483648)

print('OK!')
