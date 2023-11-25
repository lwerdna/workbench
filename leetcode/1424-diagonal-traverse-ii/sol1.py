#!/usr/bin/env python3

class Solution(object):
    def findDiagonalOrder(self, nums):
        answer = []

        queue = [(0,0)]
        while queue:
            row, col = queue.pop(0)

            print(f'row,col = {row},{col}')

            if col == 0 and row+1 < len(nums):
                queue.append((row+1, 0))

            if col < len(nums[row]):
                answer.append(nums[row][col])
                queue.append((row, col+1))

        print(answer)
        return answer

sol = Solution()
sol.findDiagonalOrder([[1,2,3],[4,5,6],[7,8,9]])
sol.findDiagonalOrder([[1,2,3,4,5],[6,7],[8],[9,10,11],[12,13,14,15,16]])
print('OK!')
