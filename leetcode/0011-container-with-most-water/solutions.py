#!/usr/bin/env python

import sys

class Solution0(object):
    # O(n^2), times out
    def maxArea(self, heights):
        record = 0
        for h in heights:
            indices = [i for i,x in enumerate(heights) if x >= h]
            volume = (max(indices) - min(indices)) * h
            record = max(record, volume)
        return record

class Solution1(object):
    def maxArea(self, heights):
        current = -1
        shoot_left = {} # size->idx where idx is minimized (leftmost)
        for i,h in enumerate(heights):
            if h > current:
                for k in range(current+1, h+1):
                    shoot_left[k] = i
                current = h

        #print('shoot left: ', shoot_left);

        current = -1
        shoot_right = {}
        for i in range(len(heights)-1, -1, -1):
            h = heights[i]
            if h > current:
                for k in range(current+1, h+1):
                    shoot_right[k] = i
                current = h

        #print('shoot right: ', shoot_right);

        record = 0
        # scan left to right
        for i,h in enumerate(heights):
            #print(f'considering height {h} from index {i} ->')
            #print(f'to get at least {h} you can go forward to {shoot_right[h]}')
            width = shoot_right[h] - i
            area = h * width
            #print(f'area: {area}')
            record = max(area, record)

        # scan right to left
        for i in range(len(heights)-1, -1, -1):
            h = heights[i]
            #print(f'considering height {h} from index {i} <-')
            #print(f'to get at least {h} you can go back to {shoot_left[h]}')
            width = i - shoot_left[h]
            area = h * width
            #print(f'area: {area}')
            record = max(area, record)

        return record

class Solution2(object):
    def maxArea(self, heights):
        best = 0
        L = 0
        R = len(heights)-1
        
        while L<R:
            hL = heights[L]
            hR = heights[R]
            best = max(best, (R-L)*min(hL, hR))
            
            if hL >= hR:
                R -= 1
            else:
                L += 1
            
        return best

if __name__ == '__main__':
    for sol in [Solution0(), Solution1(), Solution2()]:
        assert sol.maxArea([1,8,6,2,5,4,8,3,7]) == 49
        assert sol.maxArea([1,1]) == 1
        assert sol.maxArea([1,2]) == 1
    print('PASS')
