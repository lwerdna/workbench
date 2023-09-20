#!/usr/bin/env python3

from collections import Counter

class Solution:
    def compute(self, s):
        if not s: return 0
        
        seen = {s[0]}
        best = 1
        L, R = 0, 1

        while R <= len(s):
            if s[R-1] in seen:
                seen.remove(s[L])
                L += 1
            else:
                seen.add(s[R-1])
                R += 1

            best = max(best, R-L)
            
        return best

if __name__ == '__main__':
    sol = Solution()

    assert(sol.compute('')==0)
    assert(sol.compute('z')==1)
    assert(sol.compute('au')==2)
    assert(sol.compute('abcabcbb')==3)
    assert(sol.compute('abba')==2)

    print('PASS')
