#!/usr/bin/env python

from math import log

def event_probability(event, events_possible):
    return events_possible.count(event) / len(events_possible)

# compute information content given an event and a set of possible events
# (internally the probability of each event is calculated)
def information_content_A(event, events_possible):
    return -log(event_probability(event, events_possible), 2)

def information_content_B(probability):
    return -log(probability, 2)

# Shannon entropy of a random variable is the expected value of information
# content

# events_possible: an iteratable of events, with multiple entries conveying
#                  an increased probability of occurence
def entropy_A(events_possible):
    expected_value = 0
    for event in set(events_possible):
        p = event_probability(event, events_possible)
        I = information_content_A(event, events_possible)
        expected_value += p*I
    return expected_value

# probabilities: an iterable of probabilities for each event
def entropy_B(probabilities):
    assert abs(1-sum(probabilities)) < .001
    return sum(p*information_content_B(p) for p in probabilities)

if __name__ == '__main__':
    assert event_probability('light_tonight', ['dark_tonight']) == 0
    assert event_probability('dark_tonight', ['dark_tonight']) == 1
    assert event_probability('H', ['H', 'T']) == .5
    assert event_probability('A', list('AABABBAABA')) == .6

    assert information_content_A('dark_tonight', ['dark_tonight']) == 0
    assert information_content_A('H', ['H', 'T']) == 1
    assert information_content_A('HH', ['HH', 'HT', 'TH', 'TT']) == 2

    # from 3.1.1 in Machine Learning in Action
    data = [[1,1, 'yes'],
            [1,1, 'yes'],
            [1,0, 'no'],
            [0,1, 'no'],
            [0,1, 'no']]
    print(entropy_A([row[-1] for row in data]))

    print(entropy_B([2/5, 3/5]))

    # Wikipedia example
    # 2 bits of entropy (the average bits needed to convey the value)
    data = ['A', 'B', 'C', 'D']
    print(entropy_A(data))

    # modification:
    # Pr(x='A')=.7
    # Pr(x='B')=.26
    # Pr(x='C')=.2
    # Pr(x='D')=.2
    print(entropy_B([.7, .26, .02, .02]))
