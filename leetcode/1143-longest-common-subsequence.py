#!/usr/bin/env python3

import os, sys


from pprint import pprint

# dynamic programming with tabulation
#
# using recurrence:
# lcs(m, n) =
#     0                             if m==0 or n==0
#     lcs(m-1, n-1) + 1             if s[m-1] == s[n-1]
#     max(lcs(i,j+1), lcs(i+1, j))  otherwise
class Solution0(object):
    def longestCommonSubsequence(self, text1, text2):
        n1, n2 = len(text1), len(text2)
        tabs = [[0]*(n2+1) for k in range(n1+1)] # tabs[x][y] is answer for first x chars of text1, first y chars of text2

        for y in range(1, n2+1):
            for x in range(1, n1+1):
                if text1[x-1] == text2[y-1]:
                    tabs[x][y] = 1 + tabs[x-1][y-1]
                else:
                    tabs[x][y] = max(tabs[x][y-1], tabs[x-1][y])

        #pprint(tabs)
        return tabs[n1][n2]

# dynamic programming using memoization (cached recursion)
class Solution1(object):
    def lcs(self, n1, n2):
        if self.memo[n1][n2] != None:
            return self.memo[n1][n2]

        if self.text1[n1-1] == self.text2[n2-1]:
            result = 1 + self.lcs(n1-1, n2-1)
            self.memo[n1][n2] = result
            return result

        result = max(self.lcs(n1, n2-1), self.lcs(n1-1, n2))
        self.memo[n1][n2] = result
        return result

    def longestCommonSubsequence(self, text1, text2):
        self.text1, self.text2 = text1, text2
        n1, n2 = len(text1), len(text2)
        self.memo = [[0]*(n2+1)] + [[0] + [None]*(n2) for k in range(n1)]
        return self.lcs(n1, n2)

# tabulation, but only keeping two recent columns:
class Solution2(object):
    def longestCommonSubsequence(self, text1, text2):
        n1, n2 = len(text1), len(text2)
        tab_old = [0] * (n1 + 1)
        tab_new = [0] * (n1 + 1)

        for y in range(1, n2+1):
            tab_new, tab_old = tab_old, tab_new

            for x in range(1, n1+1):
                if text1[x-1] == text2[y-1]:
                    tab_new[x] = 1 + tab_old[x-1]
                else:
                    tab_new[x] = max(tab_new[x-1], tab_old[x])
       
        return tab_new[-1]

for sol in [Solution2()]:
    assert(sol.longestCommonSubsequence('abcde', 'ace') == 3)
    assert(sol.longestCommonSubsequence('abc', 'abc') == 3)

