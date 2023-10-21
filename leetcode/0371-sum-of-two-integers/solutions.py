#!/usr/bin/env python

class Solution0(object):
    def getSum(self, a, b):
        a &= 0xFFFFFFFF
        b &= 0xFFFFFFFF

        while b:
            a, b = a ^ b, (a & b) << 1

        a &= 0xFFFFFFFF
        b &= 0xFFFFFFFF

        if a & 0x80000000:
            a = -self.getSum(a ^ 0xFFFFFFFF, 1)

        return a

if __name__ == '__main__':
    import sys

    sol0 = Solution0()

    for a in range(-30, 30):
        for b in range(-30, 30):
            print(a, b)
            assert sol0.getSum(a, b) == a + b

    print('PASS')

