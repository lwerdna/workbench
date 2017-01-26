#!/usr/local/bin/python

import math

maxStep = .1
r1,r2 = 300.0, 100.0
gainIdeal = 1+r2/r1

out = 0.0
A = 5
print "gain according the equations: %f" % (1+(r2/r1))
for i in range(100):
	B = (r1/(r1+r2))*out
	
	print "iter=%02d A=%f B=%f out=%f gain=%f" % (i,A,B,out,out/A)

	outAfar = 100000.0*(A-B)
	if outAfar > out:
	    out += maxStep
	else:
	    out -= maxStep


   
