#!/usr/bin/env python

class Solution0:
    def reverseBits(self, n):
        result = 0
        for i in range(32):
            if not n:
                return result << (32-i)
            result = (result << 1) | (n & 1)
            n >>= 1
        return result

# from https://leetcode.com/problems/reverse-bits/solutions/3876610/99-beats-by-recursion/
class Solution1:
    def f(self,n,r,count):
        if n<1:
            return r<<(32-count)
        return self.f(n>>1,(r<<1)|(n&1),count+1)
    def reverseBits(self, n: int) -> int:
        return self.f(n,0,0)

# remove unnecessary recursion from above
class Solution2:
    def reverseBits(self, n):
        r, count = 0, 0
        while True:
            if n < 1:
                return r << (32-count)
            n, r, count = n >> 1, (r << 1) | (n & 1), count + 1

# divide and conquer
class Solution3:
    def f(self, n, width):
        if width == 1:
            return n
        shamt = width // 2
        left = n >> shamt
        right = n & ((1 << shamt)-1)
        return (self.f(right, shamt) << shamt) | self.f(left, shamt)

    def reverseBits(self, n):
        return self.f(n, 32)

if __name__ == '__main__':
    import timeit
    for i, sol in enumerate([Solution0(), Solution1(), Solution2(), Solution3()]):
        def go():
            assert sol.reverseBits(0b00000010100101000001111010011100) == 964176192
            assert sol.reverseBits(0b11111111111111111111111111111101) == 3221225471
        
        duration = timeit.timeit('go()', globals=globals(), number=10000)
        print(f'solution{i} took {duration}')

    print('PASS')

