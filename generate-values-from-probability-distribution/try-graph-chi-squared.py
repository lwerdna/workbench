#!/usr/bin/env python

import sys
from math import sqrt, pi, e
import random
import matplotlib.pyplot as plt

def normal_pdf(x, mean, stddev):
    return 1/(stddev * sqrt(2*pi)) * e**(-1/2 * ((x - mean)/stddev)**2)

def sample(a, b, mean, stddev):
    while True:
        x = a + random.random() * (b-a) # get value [a, b]
        y = random.random() # get value [0, 1]
        if y < normal_pdf(x, mean, stddev):
            return x

def find_interval(intervals, value):
    for i, (a,b) in enumerate(intervals):
        if a <= value < b:
            return i

if __name__ == '__main__':
    a, b = -5, 5


    k = 4 # number of normal random variables


    results = {}
    for i in range(100000):
        sum_ = 0
        for kk in range(k):
            sum_ += sample(a, b, 0, 1)**2

        sum_ = round(sum_, 1) # bin by rounding to 1 decimal

        results[sum_] = results.get(sum_, 0)+1

    xs = sorted(results.keys())
    ys = [results[x] for x in xs]
    plt.bar(xs, ys)
    plt.show()
