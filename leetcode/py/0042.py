#!/usr/bin/env python3

class Solution:
    # 36ms, 12.4mb
    def trap(self, height):
        lwalls = []
        rwalls = []
        
        record = 0
        for h in height:
            record = max(record, h)
            lwalls.append(record)
        #print('lwalls: ', lwalls)

        record = 0
        for h in reversed(height):
            record = max(record, h)
            rwalls.append(record)
        rwalls.reverse()
        #print('rwalls: ', rwalls)

        rain = 0
        for i in range(len(height)):
            tmp = min(lwalls[i], rwalls[i]) - height[i]
            if tmp > 0:
                rain += tmp

        return rain

tests = []
tests.append(([0], 0))
tests.append(([], 0))
tests.append(([0,1,0,2,1,0,1,3,2,1,2,1], 6))

sol = Solution()
for (inp, expected) in tests:
    out = sol.trap(inp)
    print('on input: ', inp, ' got output: ', out)
    if out != expected:
        print('expected: ', expected)
        assert False
