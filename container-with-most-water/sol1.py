#!/usr/bin/env python3
# "sliding window" technique

class Foo:
    @classmethod
    def compute(self, height):
    # ~~~~~ snip to leetcode

        best = 0
        L = 0
        R = len(height)-1
        
        while L<R:
            hL = height[L]
            hR = height[R]
            best = max(best, (R-L)*min(hL, hR))
            
            if hL >= hR:
                R -= 1
            else:
                L += 1
            
        return best

assert(Foo.compute([1,8,6,2,5,4,8,3,7]) == 49)
assert(Foo.compute([1,8]) == 1)
assert(Foo.compute([1,1,8]) == 2)
assert(Foo.compute([2,1,1,8]) == 6)

print('OK!')
