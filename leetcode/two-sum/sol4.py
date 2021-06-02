#!/usr/bin/env python3
# "sliding window"-like technique from sol3.py
# but instead of sorting tuples, just sort a range, 44ms -> 28ms

class Solution(object):
    def twoSum(self, nums, target):
        lookup = sorted(range(len(nums)), key=lambda x: nums[x])
        (L,R) = (0, len(nums)-1)
        while L<R:
            tmp = nums[lookup[L]] + nums[lookup[R]]
            if tmp == target:
                return [lookup[L], lookup[R]]
            elif tmp > target:
                R -= 1
            else:
                L += 1

sol = Solution()
assert(sol.twoSum([3,4,5,6,-7,8,9], -3) in [[1,4], [4,1]])
print(sol.twoSum([3,4,5,6,-7,8,9], -3))
print('OK!')
