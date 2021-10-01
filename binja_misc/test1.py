#!/usr/bin/env python

# Q: How much faster are different initial analysis options?
# A: controlFlow and basic are around a quarter, intermediate is around three quarters of full

# /bin/ls
# 1.473311s controlFlow (30.638662% of full)
# 1.694418s basic (35.236760% of full)
# 3.421868s intermediate (71.160455% of full)
# 4.808666s full (100.000000% of full)

# libpthread_x86_64.so.0
# 1.474496s controlFlow (16.929012% of full)
# 2.059575s basic (23.646425% of full)
# 6.303724s intermediate (72.374422% of full)
# 8.709878s full (100.000000% of full)

import sys, time
import binaryninja

fpath = '/bin/ls' if len(sys.argv)==1 else sys.argv[1]
update_analysis = True
callbacks = None
options = {}

# cause plugins to load, whatever else to get initialized which could interfere in measurements
print('initial open')
with binaryninja.open_view(fpath) as bv:
    pass

modes = ['controlFlow', 'basic', 'intermediate', 'full']
results = []

for mode in modes:
    options = {'analysis.mode':mode}
    print('opening with %s' % options)
    t0 = time.perf_counter()
    with binaryninja.open_view(fpath, update_analysis, callbacks, options) as bv:
        t1 = time.perf_counter()
        results.append(t1-t0)
        print('done! %fs' % results[-1])

print('results:')
for (i, mode) in enumerate(modes):
    print('%fs %s (%f%% of full)' % (results[i], mode, results[i]/results[-1]*100))
