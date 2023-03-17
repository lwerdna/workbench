#!/usr/bin/env python

import time
import random
import os, sys, re, pprint

# natural language toolkit `pip install nltk`
# https://pypi.org/project/nltk/
import nltk

def remove_nonword(x):
    return re.sub(r'[^\w]', '', x)

# Choose from the given (option, probability) pairs, respecting the probability
# example:
#     (('A', .25), ('B', .25), ('C', .5))
#     should return 'A' one-quarter of the time, 'B' one-quarter of the time, and 'C' half the time
def choose(options):
    threshold = random.random()
    accumulator = 0
    for (token, probability) in options:
        accumulator += probability
        if accumulator >= threshold:
            return token

    # accumulator should have reached 1.0 by here, necessarily >= [0,1] from random()
    assert False

def generate_sentence(lookup):
    words = []

    state = '(start)'
    while True:
        state = choose(lookup[state])
        if state in ['.', '!', '?']: break
        words.append(state)

    return ' '.join(words) + state

if __name__ == '__main__':
    print('reading book')
    t0 = time.perf_counter()
    with open('1984.txt') as fp:
        raw = fp.read()
        # multiple dashes become one space
        # ...stretch out over a long, indefinite time--weeks, possibly--and the...
        raw = re.sub(r'\-+', ' ', raw)
        # remove anything not a word character, space character, or sentence terminator: . ! ?
        raw = re.sub(r'[^\w\s\.\!\?]+', '', raw)
        # multiple spaces become one space
        raw = re.sub(r'\s+', ' ', raw)
    t1 = time.perf_counter()
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    print('tokenizing words (nltk)')
    t0 = time.perf_counter()
    words = nltk.word_tokenize(raw)
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    print('filtering words')
    t0 = time.perf_counter()
    def check(w):
        return re.match(r'^\w+$', w) or w == '.'
    words = [w for w in words if check(w)]
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    # build state machine lookup table, looks like:
    # ...
    # 'younger': (('child', 0.25),
    #             ('generation', 0.25),
    #             ('made', 0.25),
    #             ('than', 0.25)),
    # 'youngish': {('woman', 1.0)),
    # ...
    lookup = {}

    print(f'processing bigrams')
    t0 = time.perf_counter()
    counts = {w:{} for w in set(words)}
    for a,b in [(words[i], words[i+1]) for i in range(len(words)-1)]:
        subdict = counts[a]
        subdict[b] = subdict.get('b',0) + 1

    # add bigrams to lookup
    for (a, subdict) in counts.items():
        total = sum(subdict.values())
        lookup[a] = tuple((b, count/total) for (b, count) in subdict.items())
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    print('processing sentence-starting words')
    t0 = time.perf_counter()
    counts = {}
    for sentence in nltk.sent_tokenize(raw):
        i = sentence.find(' ')
        if i == -1: continue
        first_word = sentence[0:i]
        counts[first_word] = counts.get(first_word, 0) + 1

    total = sum(counts.values())
    lookup['(start)'] = tuple((w, count/total) for (w, count) in counts.items())
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    print('generating...')

    # generate sentence
    for i in range(20):
        print(generate_sentence(lookup))
        print('')

    #pprint.pprint(lookup)
    #breakpoint()
