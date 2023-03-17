#!/usr/bin/env python

import time
import random
import os, sys, re, pprint

# natural language toolkit `pip install nltk`
# https://pypi.org/project/nltk/
import nltk

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

    context = (None, '(start)')
    while True:
        word = choose(lookup[context])

        if word in ['.', '!', '?']: break
        words.append(word)

        context = (context[1], word)

    return ' '.join(words) + word

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
    lookup = {}

    print(f'processing trigrams')
    t0 = time.perf_counter()
    counts = {}
    for a,b,c in [(words[i], words[i+1], words[i+2]) for i in range(len(words)-2)]:
        bigram = (a,b)
        counts.setdefault(bigram, {})
        counts[bigram][c] = counts[bigram].get(c, 0) + 1 

    # add bigrams to lookup
    for (bigram, subdict) in counts.items():
        total = sum(subdict.values())
        lookup[bigram] = tuple((word, count/total) for (word, count) in subdict.items())
    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    # (None, '(start)') -> ???
    print('processing initial state transition')
    t0 = time.perf_counter()

    # like: { 'Foo': <how many times Foo is the first word of a sentence>,
    #         'Bar': <how many times Bar is the first word of a sentence>,
    #         ... }
    counts1 = {}

    # like: { 'Foo': {'a':<how many times a is second word after Foo>, 'b':<how many times b is second word after Foo>, ...},
    #         'Bar': {'c':<how many times a is second word after Bar>, 'd':<how many times b is second word after Bar>, ...},
    counts2 = {}
    for sentence in nltk.sent_tokenize(raw):
        words = nltk.word_tokenize(sentence)

        if len(words) > 0:
            counts1[words[0]] = counts1.get(words[0], 0) + 1

        if len(words) > 1:
            first, second = words[0], words[1]
            counts2.setdefault(first, {})
            counts2[first].setdefault(second, 0)
            counts2[first][second] += 1

    # (None, '(start)') -> ( (<FirstWordA>, <P_FirstWordA>),
    #                        (<FirstWordB>, <P_FirstWordB>), ... )
    total = sum(counts1.values())
    lookup[(None, '(start)')] = tuple((w, count/total) for (w, count) in counts1.items())

    # ('(start)', <FirstWord>) -> ( (<SecondWordA>, <P_SecondWordA>),
    #                               (<SecondWordB>, <P_SecondWordB>), ... )
    for (first, subdict) in counts2.items():
        total = sum(subdict.values())
        lookup[('(start)', first)] = tuple((second, count/total) for (second, count) in subdict.items())

    print(f'  (took {round(time.perf_counter() - t0, 4)}s)')

    print('generating...')

    # generate sentence
    for i in range(20):
        print(generate_sentence(lookup))
        print('')

    #pprint.pprint(lookup)
    #breakpoint()
