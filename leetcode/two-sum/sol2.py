#!/usr/bin/env python3
# store nums in dict, lookup -x in dict

class Solution:
    def twoSum(self, nums, target):
        lookup = {}

        for i in range(len(nums)):
            addend = nums[i]
            co_addend = target - addend
            if co_addend in lookup:
                return [lookup[co_addend], i]
            else:
                lookup[addend] = i

sol = Solution()
assert(sol.twoSum([3,4,5,6,-7,8,9], -3) == [1,4])
print('OK!')
