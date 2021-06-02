#!/usr/bin/env python
# using Algorithm L from section 7.2.1.2 from The Art of Computer Programming (TAOCP)
#
# 52ms, 12.5mb

class Solution:
    def generate(self, n):
        result = []
        if n==0: return result
        foo = list('('*n + ')'*n)
        while 1:
            # L1
            result.append(''.join(foo))
            # L2
            j = len(foo)-2
            while foo[j] >= foo[j+1]:
                j -= 1
                if j == -1: return result
            # L3
            l = len(foo)-1
            while foo[j] >= foo[l]:
                l -= 1
            (foo[j],foo[l]) = (foo[l],foo[j]) 
            # L4
            foo = foo[0:j+1] + list(reversed(foo[j+1:]))

    def generateParenthesis(self, n):
        def validate(foo):
            s = 0
            for e in foo:
                s += 1 if e=='(' else -1
                if s < 0: return False
            return True

        return list(filter(validate, self.generate(n)))

sol = Solution()
res = sol.generateParenthesis(4)
print(res)
