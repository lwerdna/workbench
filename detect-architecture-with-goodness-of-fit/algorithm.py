#!/usr/bin/env python

import os
import sys
import math

import entropy
import strings
import references

# discard 0 and normalize
def refine(data):
    data[0] = 1 # use 1 to avoid divide by 0
    s = sum(data)
    return [x/s for x in data]

def calc_chi(sampled, reference):
    total = 0
    for i in range(256):
        # if the reference amount is 0, assume we're ignore null bytes
        if reference[i] == 0:
            assert i==0
            continue
        error = (sampled[i] - reference[i])**2 / reference[i]
        total += error
    return total

def guess_architecture(fpath):
    blob = open(fpath, 'rb').read()

    entropy_scores = entropy.calculate_entropy(blob, 32)
    string_scores = strings.calculate_strings(blob, 64)

    empirical = [0]*256
    for i in range(len(blob)):
        if entropy_scores[i] > .1 and string_scores[i] < .98:
            empirical[blob[i]] += 1

    #print(empirical)
    if 0:
        import matplotlib.pyplot as plt
        plt.title(fpath)
        plt.bar(list(range(256)), refine(empirical))
        #plt.savefig('/tmp/tmp.png')
        plt.show()
        sys.exit(0)

    # normalize everything
    empirical = refine(empirical)
    counts_x86 = refine(references.counts_x86)
    counts_x86_64 = refine(references.counts_x86_64)
    counts_mips32 = refine(references.counts_mips32)
    counts_mips64 = refine(references.counts_mips64)
    counts_armv7 = refine(references.counts_armv7)
    counts_ppc = refine(references.counts_ppc)
    counts_aarch64 = refine(references.counts_aarch64)

    results = {
        'x86': calc_chi(empirical, counts_x86),
        'x86_64': calc_chi(empirical, counts_x86_64),
        'mips32': calc_chi(empirical, counts_mips32),
        'mips64': calc_chi(empirical, counts_mips64),
        'armv7': calc_chi(empirical, counts_armv7),
        'ppc': calc_chi(empirical, counts_ppc),
        'aarch64': calc_chi(empirical, counts_aarch64)
    }
    #print(results)

    # double check with scipy
    if 1:
        import scipy.stats as stats

        results2 = {}
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_x86)
        results2['x86'] = chi_square_test_statistic        
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_x86_64)
        results2['x86_64'] = chi_square_test_statistic
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_mips32)
        results2['mips32'] = chi_square_test_statistic
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_mips64)
        results2['mips64'] = chi_square_test_statistic        
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_armv7)
        results2['armv7'] = chi_square_test_statistic
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_ppc)
        results2['ppc'] = chi_square_test_statistic
        chi_square_test_statistic, p_value = stats.chisquare(empirical, counts_aarch64)
        results2['aarch64'] = chi_square_test_statistic

        assert math.isclose(results['x86'], results2['x86'])
        assert math.isclose(results['x86_64'], results2['x86_64'])
        assert math.isclose(results['mips32'], results2['mips32'])
        assert math.isclose(results['mips64'], results2['mips64'])
        assert math.isclose(results['armv7'], results2['armv7'])
        assert math.isclose(results['ppc'], results2['ppc'])
        assert math.isclose(results['aarch64'], results2['aarch64'])

        #print('PASSED SCIPY TEST')

    winner = None
    for arch in sorted(results, key=lambda k: results[k]):
        #print(f'{arch} has score {round(results[arch], 2)}')
        if not winner:
            winner = arch

    return winner
