#!/usr/bin/env python

import os
import sys

import nltk
import pandas
import wordfreq

text = open('1984.txt').read()
text = text.replace('\n', ' ')

sentences = nltk.sent_tokenize(text)

word2freq = {}
word2sents = {}

for sentence in sentences:
    words = nltk.word_tokenize(sentence)
    words = [w.lower() for w in words]
    for word in words:
        freq = wordfreq.word_frequency(word, 'en')
        if freq == 0:
            continue
        if not word.isalpha():
            continue
        word2freq[word] = wordfreq.word_frequency(word, 'en')
        word2sents[word] = word2sents.get(word, []) + [sentence]

for i, word in enumerate(sorted(word2freq, key=lambda w: word2freq[w])):
    freq = word2freq[word]
    print(f'"{word}" has frequence {freq}')
    sentences = word2sents[word]
    print(f'and appears in {len(sentences)}:')
    for s in sentences:
        print('  ' + s)
    if i > 60:
        break
    print('----')

sys.exit(0)

def calc_score(sentence):
    result = 0

    words = nltk.word_tokenize(sentence)
    for word in words:
        result += wordfreq.word_frequency(word, 'en')

    result /= len(words)

    return result

sent2score = {}
for sentence in sentences:
    sent2score[sentence] = calc_score(sentence)

def find_outliers_iqr(data):
    data = pandas.Series(data)
    q1 = data.quantile(0.25)
    q3 = data.quantile(0.75)
    iqr = q3 - q1
    lower_bound = q1 - 1.5 * iqr
    upper_bound = q3 + 1.5 * iqr
    outliers = data[(data < lower_bound) | (data > upper_bound)]
    return outliers

def find_rare_word(sentence):
    words = nltk.word_tokenize(sentence)
    words = [w for w in words if wordfreq.word_frequency(w, 'en') != 0]
    freqs = {wordfreq.word_frequency(w, 'en'):w for w in words}

    outliers = find_outliers_iqr(list(freqs))
    if len(outliers) == 1:
        outlier = outliers.values[0]
        if outlier == min(freqs):
            rare_word = freqs[outlier]
            return rare_word

for sentence in sentences:
    #word = find_rare_word(sentence)
    words = nltk.word_tokenize(sentence)
    words = [w for w in words if wordfreq.word_frequency(w, 'en') != 0]
    freqs = {wordfreq.word_frequency(w, 'en'):w for w in words}

    if len(words) < 10:
        continue

    min_freq = min(freqs)
    min_word = freqs[min_freq]

    print('sentence: ' + sentence)
    print('rareword: ' + min_word)

#for i,sentence in enumerate(sorted(sentences, key=lambda x:sent2score[x])):
#    print('> ' + sentence)
#    score = calc_score(sentence)
#    print('score:', score)
#
#    if i >= 100:
#        break
