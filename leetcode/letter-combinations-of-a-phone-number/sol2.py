#!/usr/bin/env python3

# 24ms, 11.9mb

class Solution:
    def helper(self, digits):
        if digits == '': return ['']

        lookup = {
            '2':list('abc'),
            '3':list('def'),
            '4':list('ghi'),
            '5':list('jkl'),
            '6':list('mno'),
            '7':list('pqrs'),
            '8':list('tuv'),
            '9':list('wxyz')
        }

        heads = lookup[digits[0]]

        result = []
        for head in heads:
            for subresult in self.helper(digits[1:]):
                result.append(head + subresult)

        return result
    
    def letterCombinations(self, digits):
        if digits == '': return []
        return self.helper(digits)
   
inp = "23"
inp = ''
inp = '222'
inp = '2399'

sol = Solution()
ans = sol.letterCombinations(inp)

print(ans)
