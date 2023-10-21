#!/usr/bin/env python

class Solution0(object):
    def countBits(self, n):
        if n==0: return [0]
        if n==1: return [0, 1]
        result = [0, 1]
        current = 0
        limit = 2

        for i in range(2, n+1):
            result.append(result[current]+1)

            current += 1
            if current == limit:
                current = 0
                limit = limit + limit

        return result

if __name__ == '__main__':
    import sys

    sol = Solution0()
    print(sol.countBits(0))
    print(sol.countBits(1))
    print(sol.countBits(2))
    print(sol.countBits(3))
    print(sol.countBits(4))
    print(sol.countBits(20))

    print('PASS')
