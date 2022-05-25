#!/usr/bin/env python3

# Runtime: 182 ms, faster than 43.77% of Python3 online submissions for Two Sum II - Input Array Is Sorted.
# Memory Usage: 14.9 MB, less than 42.09% of Python3 online submissions for Two Sum II - Input Array Is Sorted.

class Solution:
    def twoSum(self, numbers: List[int], target: int) -> List[int]:
        left = 0
        right = len(numbers)-1
        while True:
            result = numbers[left] + numbers[right]
            if result < target:
                left += 1
            elif result > target:
                right -= 1
            else:
                return [left+1, right+1] 

sol = Solution()
assert sol.twoSum([2,7,11,15], 9) == [1,2]
assert sol.twoSum([2,3,4], 6) == [1,3]
assert sol.twoSum([-1,0], -1) == [1,2]
