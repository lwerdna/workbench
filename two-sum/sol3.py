#!/usr/bin/env python3
# "sliding window"-like technique: sort the list, then
# adjust L: increase sum
# adjust R: decrease sum

class Solution(object):
    def twoSum(self, nums, target):
        nums = sorted(enumerate(nums), key=lambda x: x[1])

        (L,R) = (0, len(nums)-1)
        while L<R:
            tmp = nums[L][1] + nums[R][1]
            if tmp == target:
                return [nums[L][0], nums[R][0]]
            elif tmp > target:
                R -= 1
            else:
                L += 1

sol = Solution()
assert(sol.twoSum([3,4,5,6,-7,8,9], -3) in [[1,4], [4,1]])
print('OK!')
