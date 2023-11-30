#!/usr/bin/env python3

class Solution(object):
    def getSumAbsoluteDifferences(self, nums):
        N = len(nums)

        sofar = 0
        lookup = [sofar := x + sofar for x in nums]

        total = sum(nums)
        
        result = [0]*N
        for i, num in enumerate(nums):
            if i > 0:
                result[i] += nums[i] * i - lookup[i-1]
            if i < N-1:
                result[i] += total - lookup[i] - (nums[i] * (N-i-1))

        return result


sol = Solution()
print(sol.getSumAbsoluteDifferences([2, 3, 5]), '(expecting [4,3,5])')
print(sol.getSumAbsoluteDifferences([1, 4, 6, 8, 10]), '(expecting [24,15,13,15,21])')

print('OK!')
