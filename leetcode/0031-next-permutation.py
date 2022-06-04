#!/usr/bin/env python3
    
# WARNING! must be done in place, judge will check

class Solution:
    def inPlaceReverse(self, nums, L=0):
        R = len(nums)-1
        while L<R:
            (nums[L], nums[R]) = (nums[R], nums[L])
            L += 1
            R -= 1

    def nextPermutation(self, nums):
        if len(nums) <= 1: return nums

        # find rightmost element less than its right neighbor
        i = len(nums)-2
        while i>=0 and nums[i]>=nums[i+1]:
            i -= 1
        if i == -1:
            self.inPlaceReverse(nums)
            return nums
        #print('i', i)

        # find rightmost element greater than nums[i]
        j = len(nums)-1
        while nums[j]<=nums[i]:
            j -= 1
        #print('j', j)

        # swap them
        (nums[i], nums[j]) = (nums[j], nums[i])
        # reverse all after i
        self.inPlaceReverse(nums, i+1)

        # done
        return nums

tests = []
tests.append(([1,2,3], [1,3,2]))
tests.append(([3,2,1], [1,2,3]))
tests.append(([1,1,5], [1,5,1]))
tests.append(([], []))
tests.append(([1], [1]))
tests.append(([1,2], [2,1]))
tests.append(([2,1], [1,2]))
tests.append(([1,3,2], [2,1,3]))
tests.append(([1,5,1], [5,1,1]))

sol = Solution()
for (inp, expected) in tests:
    out = sol.nextPermutation(list(inp))
    print('on input: ', inp, ' got output: ', out)
    if out != expected:
        print('expected: ', expected)
        assert False
