#!/usr/bin/env python

# recurrence:
# max_theft[i] = value[i] + max(max_theft[i+2], max_theft[i+3])
#
# or, from the other direction:
# max_theft[i] = value[i] + max(max_theft[i-2], max_theft[i-3])

class Solution0:
    def rob(self, nums):
        # edge case
        if len(nums) <= 2:
            return max(nums)

        # table init
        table = [None]*len(nums)
        table[0] = nums[0]
        table[1] = nums[1]
        if len(table) >= 3:
            table[2] = nums[0] + nums[2]

        # table populate
        for i in range(3, len(table)):
            table[i] = nums[i] + max(table[i-2], table[i-3])
        
        # done
        return max(table[-1], table[-2])

if __name__ == '__main__':
    for i,sol in enumerate([Solution0()]):
        print(f'solution {i}...')
        print(sol.rob([1,2,3,1]))
        print(sol.rob([2,7,9,3,1]))

    print('PASS')
