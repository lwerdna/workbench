#!/usr/bin/env python3

class Solution0:
    def longestValidParentheses(self, s):
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


# Runtime: 86 ms, faster than 18.35% of Python3 online submissions for Longest Valid Parentheses.
# Memory Usage: 14.7 MB, less than 24.96% of Python3 online submissions for Longest Valid Parentheses.
class Solution1(object):
    def longestValidParentheses(self, s):
    # ~~~
        marks = [0]*len(s)

        # mark indices where parentheses are matched
        stack = []
        for R in range(len(s)):
            if s[R] == '(':
                stack.append(R)
            else:
                try:
                    L = stack.pop()
                    marks[L] = 1
                    marks[R] = 1
                except IndexError:
                    pass

        # count the runs
        record = 0
        i = 0
        while i < len(marks):
            run = 0
            while i < len(marks) and marks[i]:
                run += 1
                i += 1

            record = max(record, run)
            i += 1

        return record

for sol in [Solution0(), Solution1()]:
    assert(sol.longestValidParentheses('') == 0)
    assert(sol.longestValidParentheses('()') == 2)
    assert(sol.longestValidParentheses(')(') == 0)
    assert(sol.longestValidParentheses('(()') == 2)
    assert(sol.longestValidParentheses('(()') == 2)
    assert(sol.longestValidParentheses(')()())') == 4)
    assert(sol.longestValidParentheses('()(())') == 6)
    assert(sol.longestValidParentheses(')()())') == 4)
    assert(sol.longestValidParentheses(')((((((((((((((((())') == 4)
    assert(sol.longestValidParentheses(')(((()()))))()(()))())((()') == 10)
    assert(sol.longestValidParentheses('))()()()()()()()))))))))()') == 14)
