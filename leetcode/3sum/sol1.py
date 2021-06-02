#!/usr/bin/env python3
# make dict of all 2-sums a+b, then scan and search for -c
# small check for if a 2-sum a+b could POSSIBLY make the 3-sum (otherwise don't store it)
# this exceeds time limit for large input

class Foo:
    @classmethod
    def compute(self, nums):
    # ~~~~~ snip to leetcode
        lennums = len(nums)
        lowest = min(nums)
        highest = max(nums)

        print('A')
        sums = {}
        for i in range(lennums):
            for j in range(i+1, lennums):
                s = nums[i] + nums[j]
            
                # 199846 with this check
                # 383085 without this check
                if s+lowest>0 or s+highest<0: continue
            
                # sum -> source indices of addends
                if s in sums:
                    sums[s].append((i,j))
                else:
                    sums[s] = [(i,j)]

        solutions = set()               
        for k,c in enumerate(nums):
            for (i,j) in sums.get(-c, []):
                if k!=i and k!=j:
                    solutions.add(tuple(sorted((nums[i], nums[j], nums[k]))))
               
        return list(solutions)


wtf = [-4,-2,-2,-2,0,1,2,2,2,3,3,4,4,6,6]
print(len(wtf))
print(Foo.compute(wtf))

from input import longlist
print(Foo.compute(longlist))

print('OK!')
