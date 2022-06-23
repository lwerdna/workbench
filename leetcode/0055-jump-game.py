#!/usr/bin/env python3

import os, sys

from pprint import pprint

# strategy: track how much "fuel" is LEFT is travelling left-to-right
# eg: initial fuel is [2,3,1,1,4]
#     at location 0: 2 fuel left
#     at location 1: 3 fuel left (maximum of 2 from left side or the three present)
#     at location 2: 2 fuel left (maximum of 2 from left side or the 1 present)
#     at location 3: 1 fuel left (maximum of 1 from left side or the 1 present)
#     at location 4: 4 fuel left (maximum of 0 from left side or the 4 present)
#     producing:
#     [2,3,2,1,4]
#
# and the question of whether the last index is reachable is decided by if the second-to-last index has >= 1 fuel
#
# so the recurrence is:
# available_fuel_i = 0                                               if available_fuel_{i-1} <= 0
#                  = max(available_fuel_{i-1} - 1, initial_fuel_{i}) otherwise
#
# and then:
# reachable_i = available_fuel_{i-1} > 0

class Solution0:
    def canJump(self, nums):
        if len(nums) <= 1:
            return True

        table = list(nums)
        for i in range(1, len(table)):
            prev = table[i-1]

            if prev == 0:
                table[i] = 0
            else:
                table[i] = max(table[i-1] - 1, table[i])

        return table[-2] > 0

# optimizations:
# - abandon calculation early if 0 fuel ever encountered
# - keep only the most recent "fuel remaining" value
# - know at least one value will be sent

class Solution1:
    def canJump(self, nums):
        remaining = nums[0]
        for i in range(1, len(nums)):
            if not remaining:
                return False

            remaining = max(remaining-1, nums[i])

        return True

for sol in [Solution0(), Solution1()]:
    #assert(sol.canJump([]) == True)
    assert(sol.canJump([0]) == True)
    assert(sol.canJump([0,2,3]) == False)
    assert(sol.canJump([0,999]) == False)
    assert(sol.canJump([2,0,0]) == True)
    assert(sol.canJump([2,3,1,1,4]) == True)
    assert(sol.canJump([3,2,1,0,4]) == False)
