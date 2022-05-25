#!/usr/bin/env python3

# Runtime: 55 ms, faster than 72.08% of Python3 online submissions for Valid Palindrome.
# Memory Usage: 19.3 MB, less than 9.01% of Python3 online submissions for Valid Palindrome.
class Solution0:
    @classmethod
    def compute(self, s):
    # ~~~~~ snip to leetcode
        s = [c.lower() for c in s if c.isalnum()]

        L = 0
        R = len(s)-1
        while L <= R:
            if s[L] != s[R]:
                return False
            L += 1
            R -= 1

        return True

sol = Solution0()
assert(sol.compute('A man, a plan, a canal: Panama') == True)
assert(sol.compute('race a car') == False)
assert(sol.compute([' ']) == True)

print('OK!')
