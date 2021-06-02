#!/usr/bin/env python3

class Solution:
    def longestValidParenthesis(self, s):
        intervs = []
        stack = []
        for (R,c) in enumerate(s):
            if c == '(':
                stack.append(R)
                #print('after s[%d], stack: %s' % (R, stack))
            elif c == ')':
                if not stack:
                    continue
                L = stack.pop()

                # remove all intervals consumed by this one
                while intervs and intervs[-1][0] >= L:
                    intervs.pop()

                intervs.append([L,R])

        if not intervs:
            return 0

        #print('intervals after phase1: ', intervs)

        # connect any intervals like [1,2] [3,4] -> [1,4]
        tmp = []
        i = 0
        while i < len(intervs):
            new = list(intervs[i])

            while i < len(intervs)-1 and intervs[i][1]+1 == intervs[i+1][0]:
                i += 1
            new[1] = intervs[i][1]

            tmp.append(new)
            i += 1

        intervs = tmp

        #print('intervals after phase2: ', intervs)
               
        # answer is the longest interval:

        return max(map(lambda interv: interv[1]-interv[0]+1, intervs))


tests = []
tests.append(('()(())', 6))
tests.append(('', 0))
tests.append(('()', 2))
tests.append((')(', 0))
tests.append((')((((((((((((((((())', 4))
tests.append(('(()', 2))
tests.append((')()())', 4))
tests.append(('))()()()()()()()))))))))()', 14))

sol = Solution()
for (inp, expected) in tests:
    out = sol.longestValidParenthesis(inp)
    print('on input: ', inp, ' got output: ', out)
    if out != expected:
        print('expected: ', expected)
        assert False
