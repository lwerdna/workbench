#!/usr/bin/env python

class Solution0(object):
    def missingNumber(self, nums) -> int:
        largest = len(nums)
        expected_sum = (largest * (largest+1))//2
        actual_sum = sum(nums)
        return expected_sum - actual_sum

class Solution1(object):
    def missingNumber(self, nums) -> int:
        nums.sort()
        for i, n in enumerate(nums):
            if i != n:
                return i
        return len(nums)

class Solution2(object):
    def missingNumber(self, nums) -> int:
        return (set(range(len(nums)+1)) - set(nums)).pop()

class Solution3(object):
    def missingNumber(self, nums) -> int:
        lookup = {i:True for i in nums}
        for i in range(len(nums)+1):
            if not i in lookup:
                return i

class Solution4(object):
    def missingNumber(self, nums) -> int:
        memory = len(nums)
        for i, num in enumerate(nums):
            memory = memory ^ i ^ num
        return memory

from operator import xor
from functools import reduce
class Solution5(object):
    def missingNumber(self, nums) -> int:
        return reduce(xor, nums) ^ reduce(xor, range(len(nums)+1))

if __name__ == '__main__':
    test_cases = [  ([3,0,1], 2),
                    ([0,1], 2),
                    ([9,6,4,2,3,5,7,0,1], 8) ]

    import random
    for i in range(100):
        numbers = list(range(random.randint(1,10000)))
        answer = numbers.pop(random.randint(0, len(numbers)-1))
        test_cases.append((numbers, answer))

    import timeit
    for i, sol in enumerate([Solution0(), Solution1(), Solution2(), Solution3(), Solution4(), Solution5()]):
        def go():
            for numbers, answer in test_cases:
                assert sol.missingNumber(numbers) == answer

        duration = timeit.timeit('go()', number=100, globals=globals())
        print(f'solution{i} took {duration}')

