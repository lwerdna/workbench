#!/usr/bin/env python

class Solution:
    def combinationSum(self, candidates, target):
        result = []
        stack = [(0, [], target)]
        while stack:
            index, subsolution, subtarget = stack.pop()
            if subtarget == 0:
                result.append(subsolution)
            elif index<len(candidates) and subtarget > 0:
                stack.append((index, subsolution+[candidates[index]], subtarget-candidates[index])) # use candidate
                stack.append((index+1, subsolution, subtarget)) # don't use candidate
        return result

if __name__ == '__main__':
    solution = Solution()

    candidates = [2,3,6,7]
    target = 7
    print(solution.combinationSum(candidates, target))

    print('----')

    candidates = [2,3,5]
    target = 8
    print(solution.combinationSum(candidates, target))
