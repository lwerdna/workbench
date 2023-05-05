#!/usr/bin/env python

# example 3.4 using decision trees to predict lense type

import os, sys
import pprint

import entropy

column_names = ['age', 'prescr', 'astigmatic', 'tear_rate', 'lenses']

def entropy_of_data_set(data):
    classes = [row[-1] for row in data]
    return entropy.entropy_A(classes)

def data_copy(data):
    data2 = []
    for row in data:
        data2.append(list(row))
    return data2

def split(data, column):
    result = []
    for attr_value in {row[column] for row in data}:
        subset = [list(row) for row in data if row[column] == attr_value]
        for row in subset:
            row[column] = None
        result.append(subset)
    return result

def info_gain(data, column):
    before = entropy_of_data_set(data)
    after = sum(entropy_of_data_set(x) for x in split(data, column))
    return before - after

data = []
for line in open('./lenses.dat').readlines():
    age, prescr, astigmatic, tear_rate, lenses = line.strip().split('\t')
    data.append([age, prescr, astigmatic, tear_rate, lenses])

pprint.pprint(data)

gains = {column_names[col]: info_gain(data, col) for col in range(4)}
pprint.pprint(gains)
best = max(gains, key=lambda k: gains[k])
print(best)


#for result in split(data, 0):
#    print('----')
#    pprint.pprint(result)

#print(entropy_of_data_set(data))




