#!/usr/local/bin/python

import math

r1=300.0
r2=100.0
gain_internal = 100000.0

supplyHi=12

supplyLo=-1*supplyHi

# want any small diff to shoot to supply
# want supply to be approached, but not reached
# for example, see y = 7.64*atan(10x)
def gain_internal(diff):
    global supplyHi
    c = supplyHi / ((math.pi)/2) # max atan can reach
    a = 20 # accelerate approach toward
    o = c * math.atan(a*diff)
    print "diff=%f out=%f" % (diff, o)
    return o

gainIdeal = 1+r2/r1

inp = 5.0
out = 0.0
A = 5
for i in range(5):
    B = (r1/(r1+r2))*out
    out = gain_internal(A-B)
    gainCalculated = out/inp
    print "inp=%f A=%f B=%f out=%f gainC=%f gainI=%f" % (inp,A,B,out,gainCalculated,gainIdeal)

   
