#!/usr/bin/env python3

class Solution:
    def subarraySum(self, nums, k):
        n = len(nums)
        sums = list(nums)
        
        print('a')
        
        result = len([x for x in nums if x==k])
        
        print('b')
        
        for width in range(2, n+1):
            for i in range(n-width+1):
                sums[i] += nums[i+width-1]
                 
                if sums[i] == k:
                    result += 1
        
            #print(sums[0:n-width+1])

        print('c')
        return result

with open('biginput.txt') as fp:
	line = fp.readlines()[0]
	numstrs = line.split(',')
	nums = list(map(int, numstrs))
print(len(nums))
sol = Solution()
res = sol.subarraySum(nums, 100)
print("result: ", res)

