#!/usr/bin/env python3

from collections import Counter

class Solution:
    def compute(self, s):
        debug = 1
        if not s: return 0
        if len(s)==1: return 1
        
        record = 1
        L = R = 0
        lookup = set(s[L])
        ans = s[L]
        
        while 1:
            # move R
            while R<len(s)-1 and not s[R+1] in lookup:
                R += 1
                lookup.add(s[R])
            
            if debug:
                print('after R move:')    
                print('(L,R) = (%d,%d)' % (L,R))
                print(s[L:R+1])
                print(lookup)
                print('----')
            
            # make a record?
            if R-L+1 > record:
                record = R-L+1
                ans = s[L:R+1]

            # all done?
            if R == len(s)-1:
                break

            # move L
            while L<=R and s[R+1] in lookup:
                if debug:
                    print('removing %s' % s[L])
                lookup.remove(s[L])
                L += 1
            R += 1
            lookup.add(s[R])

            if debug:
                print('after L move:')    
                print('(L,R) = (%d,%d)' % (L,R))
                print(s[L:R+1])
                print(lookup)
                print('----')

        return len(ans)

if __name__ == '__main__':
    sol = Solution()

    assert(sol.compute('')==0)
    assert(sol.compute('z')==1)
    assert(sol.compute('au')==2)
    assert(sol.compute('abcabcbb')==3)
    assert(sol.compute('abba')==2)

    print('PASS')
