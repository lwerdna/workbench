#!/usr/bin/env python

class Foo(object):
    @classmethod
    def compute(self, cost):
        (a,b,c) = (0,0,min(cost[0],cost[1]))
        
        for i in range(2, len(cost)+1):
            c = min(a+cost[i-2], b+cost[i-1])
            a = b
            b = c
            
        return c

assert(Foo.compute([10, 15, 20])==15)
assert(Foo.compute([1, 100, 1, 1, 1, 100, 1, 1, 100, 1])==6)
assert(Foo.compute([10, 15])==10)
assert(Foo.compute([10, 8])==8)
print('OK!')
