#!/usr/bin/env python

class Solution:
    # candidates are sorted ascending
    # return list of lists
    def worker(self, candidates, target, memo):
        if target in memo:
            return memo[target]

        solutions = []
        #for i,c in enumerate(x for x in candidates if x<= target):
        for c in [x for x in candidates if x<= target]:
            subtarget = target-c
            if subtarget == 0:
                solutions.append([c])
            else:
                subsolutions = self.worker(candidates, subtarget, memo)
                solutions.extend([c] + ss for ss in subsolutions if ss[0]>=c)

        memo[target] = solutions
        return solutions

    def combinationSum(self, candidates, target):
        memo = {}
        return self.worker(sorted(candidates), target, memo)

if __name__ == '__main__':
    solution = Solution()

    candidates = [2,3,6,7]
    target = 7
    print(solution.combinationSum(candidates, target))

    print('----')

    candidates = [2,3,5]
    target = 8
    print(solution.combinationSum(candidates, target))
