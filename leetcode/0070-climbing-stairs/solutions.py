#!/usr/bin/env python

# recurrence: The number of ways to climb N stairs using steps of 1 or 2 is the
# number of ways to climb N-2 stairs (taking a double step after each solution)
# plus the number of ways to climb N-1 stairs (taking a single step after each
# solution)
#
# solution[N] = solution[N-2] + solution[N-1]

# bottom up, tabulation, full table allocated at beginning
class Solution0:
    def climbStairs(self, n):
        table = [1, 2] + [None]*(n-2+1)
        
        for i in range(2, n):
            table[i] = table[i-2] + table[i-1]
        
        return table[n-1]

# bottom up, tabulation, table appended to during solve
class Solution1:
    def climbStairs(self, n):
        ans = [0, 1, 2]
        if n < 3:
            return ans[n]

        for i in range(3, n+1):
            ans.append(ans[i-2] + ans[i-1])
            
        return ans[-1]

# top down, memoization
def s2help(n, memo):
    if n in memo:
        return memo[n]

    result = memo[n] = s2help(n-1, memo) + s2help(n-2, memo)
    return result

class Solution2:
    def climbStairs(self, n):
        memo = {0:0, 1:1, 2:2}
        return s2help(n, memo)

# store only the table frontier
class Solution3:
    def climbStairs(self, n):
        if n < 3:
            return n

        a = 1
        b = 2
        for i in range(3, n+1):
            c = a + b
            a = b
            b = c
            
        return c

# use closed-form solution to Fibonacci
# Unfortunately, due to accumulated rounding error, this stops working after about n=70
import math
def fib(n):
    cool = math.sqrt(5)
    return int((1/cool) * (((1+cool)/2)**n - ((1-cool)/2)**n))

class Solution4:
    def climbStairs(self, n):
        return fib(n+1)

if __name__ == '__main__':
    solutions = [Solution0(), Solution1(), Solution2(), Solution3(), Solution4()]
    for n in range(1, 45+1):
        result = None
        for i,sol in enumerate(solutions):
            tmp = sol.climbStairs(n)
            print(f'solution{i} on {n} returns {tmp}')
            if result == None:
                result = tmp
            else:
                assert tmp == result

    import timeit
    for i, sol in enumerate([Solution0(), Solution1(), Solution2(), Solution3(), Solution4()]):
        def go():
            for n in range(100):
                sol.climbStairs(n)
        duration = timeit.timeit('go()', globals=globals(), number=1000)
        print(f'solution{i} took {duration}')

    print('PASS')
