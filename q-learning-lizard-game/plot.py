#!/usr/bin/env python

import matplotlib.pyplot as plt
import numpy as np

with open('log.csv') as fp:
    steps = 0
    rows = []
    first = True
    for line in fp.readlines():
        tokens = line.strip().split(',')
        if first:
            labels = tokens
            first = False
        else:
            rows.append([float(t) for t in tokens])        
            steps += 1

figure, axes = plt.subplots(1)
# if plt.subplots() or plt.subplots(1), axes is <AxesSubplot:>
# if plt.subplots(2), axes is array([<AxesSubplot:>, <AxesSubplot:>], dtype=object)

x_values = list(range(steps))
for (column, label) in enumerate(labels):
    y_values = [row[column] for row in rows]
    axes.plot(x_values, y_values)
    
axes.set_title('Q-value vs step')
axes.set_ylabel("Q-value ")
axes.set_xlabel("step ")

figure.set_figwidth(12.8)
figure.set_figheight(4.8)
figure.legend(labels)
figure.savefig('plot.svg', format='svg', dpi=1200, bbox_inches='tight')
