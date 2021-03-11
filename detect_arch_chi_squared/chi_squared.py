#!/usr/bin/env python

def chi_square(a, b):
	# https://github.com/opencv/opencv/blob/master/modules/imgproc/src/histogram.cpp
	# sum(i=1,n, (x_i - y_i)^2 / (x_i+y_i) )

	assert len(a)==len(b)
	result = 0;
	for i in range(len(a)):
		numerator = a[i]-b[i]
		denominator = a[i] + b[i]
		if denominator != 0:
			result += 1.0 * (a[i]-b[i])**2 / (a[i]+b[i])
	return result

def normalize(a):
	s = float(sum(a))
	return list(map(lambda x: x/s, a))

def cmp_histograms(a, b):
	return chi_square(normalize(a), normalize(b))
