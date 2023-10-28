#!/usr/bin/env python3

import itertools

# Algorithm L from TAOCP Volume 4A, section 7.2.1.2
class Solution0:
    def search(self, n):
        if n==0: return ['']
        result = []
        foo = list('('*n + ')'*n)
        while 1:
            # L1
            result.append(''.join(foo))
            # L2
            j = len(foo)-2
            while foo[j] >= foo[j+1]:
                j -= 1
                if j == -1: return result
            # L3
            l = len(foo)-1
            while foo[j] >= foo[l]:
                l -= 1
            (foo[j],foo[l]) = (foo[l],foo[j])
            # L4
            foo = foo[0:j+1] + list(reversed(foo[j+1:]))

    def generateParenthesis(self, n):
        def validate(foo):
            s = 0
            for e in foo:
                s += 1 if e=='(' else -1
                if s < 0: return False
            return True

        return list(filter(validate, self.search(n)))

# TOO SLOW afteer n>=6
# generate, then filter
class Solution1:
    def generateParenthesis(self, n):
        def validate(foo):
            s = 0
            for e in foo:
                s += 1 if e=='(' else -1
                if s < 0: return False
            return True

        starter = '()'*n
        perms = [''.join(x) for x in itertools.permutations(starter) if validate(x)]
        return list(set(perms))

class Solution2:
    def search(self, n, x=0, y=0, sol=''):
        if x < y:
            return []
        if x < n:
            self.search(n, x+1, y, sol+'(')
        if y < n:
            self.search(n, x, y+1, sol+')')
        if (x, y) == (n, n):
            self.result.append(sol)

    def generateParenthesis(self, n):
        if n == 0: return ['']
        self.result = []
        self.search(n)
        return self.result

# bottom-up computation, calculating the frontier of the accumulation graph
class Solution3:
    def generateParenthesis(self, n):
        row = [['('*i] for i in range(n+1)]

        while len(row) > 1:
            new = [None] * (len(row)-1)
            for i in range(len(new)):
                new[i] = [x + ')' for x in row[i+1]]
                if i:
                    new[i] = [x + '(' for x in new[i-1]] + new[i]
            row = new

        return row[0]

# top-down recursion
class Solution4:
    def search(self, length, surplus=0):
        assert surplus <= length

        if length == 0:
            return ['']
        if length == surplus:
            return ['('* length]

        result = []
        if surplus > 0:
            result += [x + '(' for x in self.search(length-1, surplus-1)] # increase deficits
        if surplus < length:
            result += [x + ')' for x in self.search(length-1, surplus+1)] # decrease surpluses

        return result

    def generateParenthesis(self, n):
        return self.search(2*n)

# leetcode's "closure number" approach
# each VPS length n has str[0]=='(' and str[R]==')' for some R<n
# it looks like '(A)B' where A and B are length 0,2,4,...
class Solution5:
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

class Solution5:
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

# closure number with memoization
class Solution6:
    def generate(self, length, memo):
        if length in memo:
            return memo[length]

        results = []
        for R in range(1,length,2):
            for A in self.generate(R-1, memo):
                for B in self.generate(length-R-1, memo):
                    results.append('(%s)%s' % (A,B))

        memo[length] = results
        return results

    def generateParenthesis(self, n):
        return self.generate(2*n, {0:['']})

# bottom-up computation, calculating the frontier of the accumulation graph
class Solution7:
    def generateParenthesis(self, n):
        #if n==2:
        #    breakpoint()

        row = [['('*i] for i in range(n+1)]

        for i in range(1, n+1):
            for j in range(i, n+1):
                row[j] = [x+')' for x in row[j]]
            for j in range(i+1, n+1):
                row[j] += [x+'(' for x in row[j-1]]

        return row[n]

if __name__ == '__main__':
    # do all solutions agree?
    solutions = [Solution0(), Solution2(), Solution3(), Solution4(), Solution5(), Solution6(), Solution7()]
    for n in range(8):
        result = None
        for i,sol in enumerate(solutions):
            tmp = sol.generateParenthesis(n)
            tmp.sort()
            #print(f'{sol} on {n} returns {tmp}')
            if result == None:
                result = tmp
            else:
                assert tmp == result

    import timeit
    for sol in solutions:
        def go():
            for n in range(8):
                sol.generateParenthesis(n)
        duration = timeit.timeit('go()', globals=globals(), number=1000)
        print(f'{sol} took {duration}')

    print('PASS')
