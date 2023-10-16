class Solution0(object):
    def climbStairs(self, n):
        memo = [1, 2] + [None]*(n-2+1)
        
        for i in range(2, n):
            memo[i] = memo[i-2] + memo[i-1]
        
        return memo[n-1]

class Solution1(object):
    def climbStairs(self, n):
        ans = [0, 1, 2]
        if n < 3:
            return ans[n]

        for i in range(3, n+1):
            ans.append(ans[i-2] + ans[i-1])
            
        return ans[-1]
