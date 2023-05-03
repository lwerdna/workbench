#!/usr/bin/env python

import sys, math
from collections import defaultdict

import matplotlib
import matplotlib.pyplot as plt

# return the most frequently occuring element, or None in the event of a tie
def plurality(l):
    counts = defaultdict(lambda: 0)
    for item in l:
        counts[item] += 1
    sorted_items = sorted(counts, key=lambda item: counts[item], reverse=True)
    if len(sorted_items) > 1 and counts[sorted_items[0]] == counts[sorted_items[1]]:
        return None
    return sorted_items[0]

assert(plurality([1,2,3]) == None)
assert(plurality([1,2,2,3]) == 2)
assert(plurality(['a','b','c']) == None)
assert(plurality(['a','b','c','d','c']) == 'c')
assert(plurality(list('aabbbcdeeefghh')) == None)
assert(plurality(list('aabbbbcdeeefghh')) == 'b')

def classify(subject, data, k=1):
    x0, y0, z0 = subject        
    distances = [math.sqrt((x1-x0)**2 + (y1-y0)**2 + (z1-z0)**2) for (x1,y1,z1,_) in data]
    indices = sorted(range(len(data)), key=lambda i: distances[i])
    k_neighbors = [data[i] for i in indices[0:k]]
    result = plurality(row[3] for row in k_neighbors)
    if result != None:
        # if there's a plurality, return!
        return result
    else:
        # otherwise, closest neighbor gets the vote
        return k_neighbors[0][3]

if __name__ == '__main__':
    data = []

    for line in open('./helens-preferences.dat').readlines():
        miles, games, icecream, label = line.strip().split('\t')
        data.append([float(miles), float(games), float(icecream), label])

    # normalize, otherwise you'd get unjustified influence from data like frequent flyer miles
    for i in range(3):
        column = [row[i] for row in data]
        d = max(column) - min(column)
        for row in data:
            row[i] /= d

    # take the last 10% of entries as test subjects
    assert len(data) == 1000

    subjects = data[900:]
    data = data[0:900]

    x_vals = []
    y_vals = []

    for k in range(1,10):
        x_vals.append(k)

        correct = 0
        for (miles, games, icecream, correct_label) in subjects:
            classified_label = classify((miles, games, icecream), data, k)

            #print(f'miles={round(miles,2)} games={round(games,2)} icecream={round(icecream,2)} label="{correct_label}" classified to "{classified_label}"...', end='')
            if classified_label == correct_label:
                #print('RIGHT!')
                correct += 1
            else:
                #print('WRONG!')
                pass

        print(f'k={k} performance {correct}/100 or {correct}%')
        y_vals.append(correct)

    # plot it
    fig, ax = plt.subplots(1)
    ax.set_xlabel('k neighbors')
    ax.set_ylabel('# correct')
    ax.plot(x_vals, y_vals)
    plt.savefig('k-versus-results.svg')
    plt.savefig('k-versus-results.png')
    plt.close(fig)


