#!/usr/bin/env python3

import os, sys

# use the recurrence:
# palindrome(L, R) =
# {
#     palindrome(L+1, R-1) + 2    if s[L]==s[R]
#                            0    otherwise
# }
class Solution0(object):
    def longestPalindrome(self, s):
        """
        :type s: str
        :rtype: str
        """
        if len(s) == 0: return ''
        if len(s) == 1: return s[0]
        
        record = -1
        ans = ''
        
        lookup = [[0]*len(s) for k in range(len(s))]
        
        for width in range(0,len(s)):
#            print('width: %d -----' % width)
            for i in range(0, len(s) - width):
                j = i + width
                
#               print('assigning (%d,%d)' % (i,j))
                if i==j:
                    result = True
                elif j==i+1:
                    result = s[j]==s[i]
                else:
                    result = lookup[i+1][j-1] and s[i]==s[j]
                
                lookup[i][j] = result
                if result and j-i>record:
                    record = j-i
                    ans = s[i:j+1]

        return ans

class Solution1:
    def longestPalindrome(self, s):
        n = len(s)
        memo = [[0]*n for i in range(n)]
        record = s[0]

        # seed: each single character is a palindrome size 1
        for i in range(n):
            memo[i][i] = 1

        # seed: each "XX" is a palindrome size 2
        for i in range(n-1):
            if s[i] == s[i+1]:
                memo[i][i+1] = 2
                if len(record) < 2:
                    record = s[i:i+2]

        # calculate the rest
        for width in range(2, n):
            for L in range(n):
                R = L + width

                try:
                    if s[L] == s[R]:
                        subpal = memo[L+1][R-1]
                        if subpal:
                            plen = subpal + 2 
                            memo[L][R] = plen
                            if plen > len(record):
                                record = s[L:R+1]

                except IndexError:
                    pass

        return record

# let memo[R] hold a list of lengths of palindromes ending at R
#
# now the recurrence:
# memo[i] = [ plen + 2 if s[i] == s[i-plen-1] ]     for each plen in memo[i-1]
# 
class Solution2(object):
    def longestPalindrome(self, s):
        n = len(s)
        longest = 1
        memo = [[1] for k in range(n)]

        # seed memo with 2 for "XX" palindromes
        for i in range(1, n):
            if s[i] == s[i-1]:
                memo[i].append(2)
                longest = max(longest, 2)

        #
        for R in range(2, n):
            for width in memo[R-1]:
                L = R - width - 1
                if L < 0: continue
                if s[R] == s[L]:
                    memo[R].append(width+2)
                    longest = max(longest, width+2)

        # find the first substring that's longest
        result = ''
        for R in range(longest-1, n):
            if longest in memo[R]:
                result = s[R-longest+1:R+1]
                break

        return result

# first, RLE the incoming string
class Solution3(object):
    def longestPalindrome(self, s):
        # RLE the string, like 'aabbc' -> [(2,'a'), (2,'b'), (1,'c')]
        elems = []
        L, cur = None, None
        for (i,c) in enumerate(s):
            if c != cur:
                if cur: elems.append((i-L, cur))
                L, cur = i, c
        if cur: elems.append((len(s)-L, cur))

        print(elems)
        breakpoint()

def seek(s, L, R):
    flag = False
    while L >= 0 and R < len(s) and s[L] == s[R]:
        flag = True
        L,R = L-1, R+1
    return s[L+1:R] if flag else ''

class Solution4(object):
    def longestPalindrome(self, s):
        best = ''
        for i in range(len(s)):
            best = max(best, seek(s, i, i), key=len)
            best = max(best, seek(s, i-1, i), key=len)
        return best

for sol in [Solution0(), Solution1(), Solution2(), Solution4()]:
    assert(sol.longestPalindrome('aacabdkacaa') == 'aca')
    assert(sol.longestPalindrome('abbaacaabbabbaacacaaabbbabbbbcba') == 'acaabbabbaaca')
    assert(sol.longestPalindrome('cbbd') == 'bb')
    assert(sol.longestPalindrome('ccc') == 'ccc')
    assert(sol.longestPalindrome('babab') == 'babab')
    assert(sol.longestPalindrome('babad') == 'bab')
    assert(sol.longestPalindrome("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd") == "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")

