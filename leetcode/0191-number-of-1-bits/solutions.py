#!/usr/bin/env python

class Solution0(object):
    def hammingWeight(self, n):
        count = 0
        while n:
            count += n & 1
            n >>= 1
        return count

class Solution1(object):
    def hammingWeight(self, n):
        n = ((n & 0xAAAAAAAA) >> 1) + (n & 0x55555555)
        n = ((n & 0xCCCCCCCC) >> 2) + (n & 0x33333333)
        n = ((n & 0xF0F0F0F0) >> 4) + (n & 0x0f0f0f0f)
        n = ((n & 0xFF00FF00) >> 8) + (n & 0x00FF00FF)
        n = ((n & 0xFFFF0000) >> 16) + (n & 0x0000FFFF)
        return n

if __name__ == '__main__':
    import sys

    sol0 = Solution0()
    sol1 = Solution1()

    for i in range(10000):
        a = sol0.hammingWeight(i)
        b = sol1.hammingWeight(i)
        print(i, a, b)
        assert a == b

    print('PASS')

