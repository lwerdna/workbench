#!/usr/bin/env python3

class Solution0(object):
    def getSumAbsoluteDifferences(self, nums):
        N = len(nums)

        sofar = 0
        lookup = [sofar := x + sofar for x in nums]

        total = sum(nums)
        
        result = [0]*N
        for i, num in enumerate(nums):
            if i > 0:
                result[i] += nums[i] * i - lookup[i-1]
            if i < N-1:
                result[i] += total - lookup[i] - (nums[i] * (N-i-1))

        return result

class Solution1(object):
    def getSumAbsoluteDifferences(self, nums):
        N = len(nums)

        sofar = 0
        lookup = [sofar := x + sofar for x in nums]

        total = sum(nums)
        
        result = [0]*N
        for i, num in enumerate(nums):
            rect_left = i * nums[i] # width * height
            rect_right = (N-i-1) * nums[i] # width * height

            if i > 0:
                result[i] += rect_left - lookup[i-1]
            result[i] += (total - lookup[i]) - rect_right

        return result

class Solution2(object):
    def getSumAbsoluteDifferences(self, nums):
        N = len(nums)
        result = [sum(nums[i]-nums[0] for i in range(1,N))]
        
        for i in range(1, N):
            delta = nums[i] - nums[i-1]
            result.append(result[-1] + i*delta - (N-i)*delta)

        return result

class Solution3(object):
    def getSumAbsoluteDifferences(self, nums):
        N = len(nums)
        result = [sum(nums[i]-nums[0] for i in range(1,N))]
        
        for i in range(1, N):
            delta = nums[i] - nums[i-1]
            result.append(result[-1] + delta*(i+i-N))

        return result

class Solution4(object):
    def getSumAbsoluteDifferences(self, nums):
        result = [sum(nums) - len(nums)*nums[0]]
        for i in range(1, len(nums)):
            result.append(result[-1] + (nums[i] - nums[i-1]) * (i+i-len(nums)))
        return result

for i,sol in enumerate([Solution0(), Solution1(), Solution2(), Solution3(), Solution4()]):
    print(f'Solution{i}():')
    print(sol.getSumAbsoluteDifferences([2, 3, 5]), '(expecting [4,3,5])')
    print(sol.getSumAbsoluteDifferences([1, 4, 6, 8, 10]), '(expecting [24,15,13,15,21])')

print('OK!')
