#!/usr/bin/env python3

import itertools

# recurrence:
#
# numDecodings(S) = 1 + numDecodings(S[1:])
#                   + 2 + numDecodings(S[2:]) if S[0:2] is a code

class Solution0:
    def singleNumber(self, nums):
        mydict = {}

        for num in nums:
            if not num in mydict:
                mydict[num] = 1
            else:
                mydict[num] = mydict[num] + 1

        for i in mydict:
            if mydict[i] == 1:
                return i

if __name__ == '__main__':
    s = Solution0()
    print(s.singleNumber([2,2,1]))
    print(s.singleNumber([4,1,2,1,2]))
    print(s.singleNumber([1]))

    print('PASS')
