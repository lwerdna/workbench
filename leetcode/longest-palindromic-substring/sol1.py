#!/usr/bin/env python3

class Solution:
    def compute(self, s):
        if len(s) == 0: return ''
        if len(s) == 1: return s[0]
        
        record = -1
        ans = ''
        lookup = {}           
        for width in range(0,len(s)):
            #print('width: %d -----' % width)
            for i in range(0, len(s) - width):
                j = i + width
                
                #print('looking up (%d,%d)' % (i,j))
                if i==j:
                    result = True
                elif j==i+1:
                    result = s[j]==s[i]
                else:
                    result = lookup[(i+1,j-1)] and s[i]==s[j]
                
                lookup[(i,j)] = result
                if result and j-i>record:
                    record = j-i
                    ans = s[i:j+1]

        return ans
        
inp = "babad" # "bab" or "aba"
inp = "cbbd" # "bb"
inp = "forgeeksskeegfor"
inp = "aaaa" # "aaaa"
inp = "ababababababa" #"ababababababa"
inp = "ac"
inp = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
sol = Solution()
ans = sol.compute(inp)
print(ans)
#import sys
#sys.exit(-1)
assert(sol.compute('babad') == 'bab')
assert(sol.compute('cbbd') == 'bb')
assert(sol.compute('forgeeksskeegfor') == 'geeksskeeg')
assert(sol.compute('aaaa') == 'aaaa')
assert(sol.compute('ababababababa') == 'ababababababa')
print(ans)
