#!/usr/bin/env python3

# Runtime: 52 ms, faster than 40.39% of Python3 online submissions for Longest Common Prefix.
# Memory Usage: 14 MB, less than 49.93% of Python3 online submissions for Longest Common Prefix.
class Solution0:
    def longestCommonPrefix(self, strs):
        try:
            for R in range(200):
                char = strs[0][R]
                if any(s[R] != char for s in strs):
                    break
        except Exception:
            pass

        return strs[0][0:R]

for sol in [Solution0()]:
    assert(sol.longestCommonPrefix(['a']) == 'a')
    assert(sol.longestCommonPrefix(['ab', 'a']) == 'a')
    assert(sol.longestCommonPrefix(['dog', 'racecar', 'car']) == '')
    assert(sol.longestCommonPrefix(['flower', 'flow', 'flight']) == 'fl')

