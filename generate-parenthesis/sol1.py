#!/usr/bin/env python
# using recursive backtracking
#
# 20ms, 11.9mb

class Solution:
    def generate(self, n, coords=(0,0), sol=''):
        if coords[0] < coords[1]:
            return
        if coords[0] < n:
            self.generate(n, (coords[0]+1, coords[1]), sol+'(')
        if coords[1] < n:
            self.generate(n, (coords[0], coords[1]+1), sol+')')
        if coords == (n,n):
            self.result.append(sol)

    def generateParenthesis(self, n):
        if n==0: return []
        self.result = []
        self.generate(n)
        return self.result

sol = Solution()
res = sol.generateParenthesis(4)
print(res)
