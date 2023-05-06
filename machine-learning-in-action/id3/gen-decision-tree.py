#!/usr/bin/env python

import os, sys
import pprint

import entropy

column_names = ['age', 'prescr', 'astigmatic', 'tear_rate', 'lenses']

#------------------------------------------------------------------------------
# data table helpers
#------------------------------------------------------------------------------

def entropy_of_data_set(data):
    classes = [row[-1] for row in data]
    return entropy.entropy_A(classes)

def split(data, column):
    result = {}
    for attr_value in {row[column] for row in data}:
        subset = [list(row) for row in data if row[column] == attr_value]
        for row in subset:
            row[column] = None
        result[attr_value] = subset
    return result

#------------------------------------------------------------------------------
# decision tree builder
#------------------------------------------------------------------------------

def info_gain(data, column):
    before = entropy_of_data_set(data)

    after = 0
    for subset in split(data, column).values():
        proportion = len(subset) / len(data)
        after += proportion * entropy_of_data_set(subset)

    return before - after

def build_decision(data):
    assert len(data) > 0

    if len(set([row[-1] for row in data]))==1:
        return {'type':'class', 'result':data[0][-1]}

    best_col, best_gain = None, None
    for col in range(4):
        gain = info_gain(data, col)
        print(f'column {col} ("{column_names[col]}") has information gain {gain}')
        if best_col == None or gain > best_gain:
            best_col, best_gain = col, gain

    result = {'type':'decision', 'attribute':column_names[best_col], 'children':{}}
    for attr_val, subdata in split(data, best_col).items():
        result['children'][attr_val] = build_decision(subdata)

    return result

#------------------------------------------------------------------------------
# DOT/graphviz funcitons
#------------------------------------------------------------------------------
def tree_dot_vertices(tree):
    result = []
    match tree['type']:
        case 'decision':
            result.append(f'{id(tree)} [shape="diamond" label="{tree["attribute"]}"];')
            for c in tree['children'].values():
                result.extend(tree_dot_vertices(c))
        case 'class':
            result.append(f'{id(tree)} [label="{tree["result"]}"];')
    return result

def tree_dot_edges(tree):
    result = []
    if tree['type'] == 'decision':
        for attr_val, child in tree['children'].items():
            result.append(f'{id(tree)} -> {id(child)} [label="{attr_val}"];')
            result.extend(tree_dot_edges(child))
    return result

def tree_to_dot(tree):
    print('digraph G {')
    print('// nodes')
    print('\n'.join(tree_dot_vertices(tree)))
    print('// edges')
    print('\n'.join(tree_dot_edges(tree)))
    print('}')

#------------------------------------------------------------------------------
# main
#------------------------------------------------------------------------------

if __name__ == '__main__':
    data = []
    for line in open('./lenses.dat').readlines():
        age, prescr, astigmatic, tear_rate, lenses = line.strip().split('\t')
        data.append([age, prescr, astigmatic, tear_rate, lenses])

    tree = build_decision(data)

    pprint.pprint(tree)

    tree_to_dot(tree)
