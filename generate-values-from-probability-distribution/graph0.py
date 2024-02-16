#!/usr/bin/env python

import math
import random
import itertools
import os, sys, re, pprint

# p is the probability of success
# n is the number of trials
def binomial_distrib(p, n):
    result = []
    for successes in range(0, n+1):
        result.append(math.comb(n, successes) * p**successes * (1-p)**(n-successes))
    return result

def find_interval(intervals, value):
    for i, (a,b) in enumerate(intervals):
        if a <= value and value < b:
            return i
    
if __name__ == '__main__':
    pdf = binomial_distrib(.5, 4)
    print(f'pdf: {pdf}')
    cdf = list(itertools.accumulate(pdf))
    print(f'cdf: {cdf}')
    intervals = list(zip([0]+cdf, cdf))
    print(f'intervals: {intervals}')

    for i in range(20):
        location = random.random()
        idx = find_interval(intervals, location)
        print(f"{idx} since random()=={location:.04f} is in {intervals[idx]} which is the {idx}'th interval")

    xs = [0,1,2,3,4]
    ys = [0,0,0,0,0]
    for i in range(10000):
        location = random.random()
        idx = find_interval(intervals, location)
        ys[idx] += 1

    import matplotlib.pyplot as plt
    plt.bar(xs, ys)
    plt.show()
