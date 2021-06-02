#!/usr/bin/env python3
# naive O(n^2) solution

class Solution(object):
    def twoSum(self, nums, target):
        """
        :type nums: List[int]
        :type target: int
        :rtype: List[int]
        """
        for i in range(len(nums)):
            for j in range(i+1,len(nums)):
                if nums[i] + nums[j] == target:
                    return [i, j]

sol = Solution()
assert(sol.twoSum([3,4,5,6,-7,8,9], -3) == [1,4])
print('OK!')
