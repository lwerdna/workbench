#!/usr/bin/env python3

# 20ms, 11.9mb

class Solution(object):
    def isValid(self, s):
        """
        :type s: str
        :rtype: bool
        """
        try:
            stack = list()
            for char in s:
                if char=='(' or char=='{' or char=='[':
                    stack.append(char)
                elif char==')':
                    assert stack.pop() == '('
                elif char=='}':
                    assert stack.pop() == '{'
                elif char==']':
                    assert stack.pop() == '['
            assert len(stack) == 0
        except Exception:
            return False
        
        return True
        
sol = Solution()
assert(sol.isValid('()'))
assert(sol.isValid('{}'))
assert(sol.isValid('[]'))
assert(sol.isValid('[') == False)
assert(sol.isValid('[(])') == False)
assert(sol.isValid('()[]{}'))
assert(sol.isValid('(]') == False)
assert(sol.isValid('([)]') == False)
assert(sol.isValid('{[]}') == True)

ans = ''
print(ans)
