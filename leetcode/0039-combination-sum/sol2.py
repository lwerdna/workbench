#!/usr/bin/env python

class Solution:
    def combinationSum(self, candidates, target):
        result = []
        def search(addends, subsolution, subtarget):
            if subtarget == 0: result.append(subsolution)
            if subtarget <= 0: return
            for i,c in enumerate(addends):
                search(addends[i:], subsolution+[c], subtarget-c)
        search(candidates, [], target)
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
