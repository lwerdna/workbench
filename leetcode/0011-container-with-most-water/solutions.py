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

# make lookup table of how far left you can go and still get some height
#                  and how far right you can go and still get some height
#
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

# "sliding window", very optimized version of Solution3
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

# recursive solution with memoization
class Solution3(object):
    def __init__(self):
        self.memo = {}

    def helper(self, heights, left, right):
        if (left, right) in self.memo:
            return self.memo[(left, right)]

        if left >= right:
            return 0

        answer = (right - left) * min(heights[left], heights[right])

        # if the left height is limiting the answer
        if heights[left] < heights[right]:
            # you'll find no better area by reducing the right (contracting width), 
            answer = max(answer, self.helper(heights, left+1, right))
        else:
            # similar argument if the right height is limiting the answer
            answer = max(answer, self.helper(heights, left, right-1))

        self.memo[(left, right)] = answer
        return answer

    def maxArea(self, heights):
        return self.helper(heights, 0, len(heights)-1)

class Solution4(object):
    def maxArea(self, heights):
        current = -1
        shoot_left = {} # height -> leftmost index
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

import bisect

class Solution4(object):
    def maxArea(self, heights):
        # the left marks are (height, i) pairs where i is the leftmost index where you can find at least height
        # eg: [1,8,6,2,5,4,8,3,7] results in [(1,0), (8,1)]
        lmarks = []
        maximum = -1
        for i, height in enumerate(heights):
            if height > maximum:
                maximum = height
                lmarks.append((height, i))

        # the right marks are (height, i) pairs where i is the rightmost index where you can find at least height
        # eg: [1,8,6,2,5,4,8,3,7] results in [(7,8), (8,6)]
        rmarks = []
        maximum = -1
        for i in reversed(range(len(heights))):
            if heights[i] > maximum:
                maximum = heights[i]
                rmarks.append((heights[i], i))

        result = 0

        # now scan right, using the marks to find how far you could go and still get desired height
        for left, height in enumerate(heights):
            insert_point = bisect.bisect_left(rmarks, height, key=lambda x: x[0])
            _, right = rmarks[insert_point]
            #print(f'searching right for {height} in {rmarks} yields {insert_point} and right {right}, for profit {height * (right-left)}')
            result = max(result, height * (right - left))

        # now scan left, using the marks to find how far you could go and still get desired height
        for right in reversed(range(len(heights))):
            height = heights[right]
            insert_point = bisect.bisect_left(lmarks, height, key=lambda x: x[0])
            _, left = lmarks[insert_point]
            #print(f'searching left for {height} in {rmarks} yields {insert_point} and left {left}, for profit {height * (right-left)}')
            result = max(result, height * (right - left))

        return result

if __name__ == '__main__':
    sol = Solution4()
    sol.maxArea([1,8,6,2,5,4,8,3,7])

    for sol in [Solution0(), Solution1(), Solution2(), Solution3(), Solution4()]:
        assert sol.maxArea([1,8,6,2,5,4,8,3,7]) == 49
        assert sol.maxArea([1,1]) == 1
        assert sol.maxArea([1,2]) == 1
    print('PASS')
