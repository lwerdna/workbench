#!/usr/bin/env python3

# leetcode's "closure number" approach
# each VPS length n has str[0]=='(' and str[R]==')' for some R<n
# it looks like '(A)B' where A and B are length 0,2,4,...

# 20ms, 11.9mb

class Solution:
    def generate(self, n):
        if n==0: return ['']
        results = []
        for R in range(1,n,2):
            for A in self.generate(R-1):
                for B in self.generate(n-R-1):
                    results.append('(%s)%s' % (A,B))
                
        return results

    def generateParenthesis(self, n):
        return self.generate(2*n)

inp = 6
sol = Solution()
for ans in sol.generateParenthesis(inp):
    print(ans)

