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

    # just plot the probability density function
    if 0:
        n = 1000
        xs = [a + 1/n * (b-a)*x for x in range(n)]
        ys = [normal_pdf(x, 0, 1) for x in xs]
        plt.plot(xs, ys)
        plt.show()

    #
    bins_n = 200
    starts = [a+(b-a)/bins_n * x for x in range(bins_n)]
    intervals = list(zip(starts, starts[1:]+[b]))
    #print(intervals)

    xs = [a+(b-a)/2 for (a,b) in intervals]
    ys = [0]*bins_n

    for i in range(100000):
        s = sample(a, b, 0, 1)
        idx = find_interval(intervals, s)
        #print(f'sample {s} was found in the {idx}th interval: {intervals[idx]}')
        ys[idx] += 1

    plt.bar(xs, ys)
    plt.show()
