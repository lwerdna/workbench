#!/usr/bin/env python

class Solution:
    def worker(self, candidates, target, memo):
        result = []
        for c in candidates:
            subtarget = target-c

            if subtarget == 0:
                result.append([c])
                continue
            if subtarget < 0:
                continue

            if subtarget in memo:
                subsolutions = memo[subtarget]
            else:
                subsolutions = self.worker(candidates, subtarget, memo)
            
            for ss in subsolutions:
                if ss[0] >= c:
                    result.append([c]+ss)

        if result:
            memo[target] = memo.get(target, []) + result

        return result

    def combinationSum(self, candidates, target):
        memo = {}
        return self.worker(candidates, target, memo)

if __name__ == '__main__':
    solution = Solution()

    candidates = [2,3,6,7]
    target = 7
    print(solution.combinationSum(candidates, target))

    print('----')

    candidates = [2,3,5]
    target = 8
    print(solution.combinationSum(candidates, target))
