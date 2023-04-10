#!/usr/bin/env python

import os
import sys
import math
import json

import matplotlib.pyplot as plt
import numpy as np

with open(sys.argv[1]) as fp:
    results = json.load(fp)

import cairo

# draw the policy
fname = 'policy.svg'
with cairo.SVGSurface('policy.svg', 1200, 1200) as surface:
    context = cairo.Context(surface)

    for state in range(37):
        center_x = (state % 12)*100 + 50
        center_y = (state // 12)*100 + 50

        context.set_source_rgba(0, 0, 0, 1)
        context.set_line_width(2)
        context.rectangle(center_x-50, center_y-50, 100, 100)
        context.stroke()

        qvals = results['qtable'][str(state)]

        tmp = [qv / sum(qvals) for qv in qvals]
        tmp = [1/qv for qv in tmp]
        tmp = [qv / sum(tmp) for qv in tmp]

        best = max([0,1,2,3], key=tmp.__getitem__)

        print(f'state {state} to {center_x},{center_y} tmp:{tmp} check:{sum(tmp)}')

        for action in range(4):
            # smallest
            alpha = (tmp[action])**1.5
            context.set_source_rgba(0, 0, 1, alpha)
            match action:
                case 0: # up
                    context.move_to(center_x, center_y-50)
                    context.line_to(center_x+25, center_y-25)
                    context.line_to(center_x-25, center_y-25)
                case 1: # right
                    context.move_to(center_x+50, center_y)
                    context.line_to(center_x+25, center_y+25)
                    context.line_to(center_x+25, center_y-25)
                case 2: # down
                    context.move_to(center_x, center_y+50)
                    context.line_to(center_x+25, center_y+25)
                    context.line_to(center_x-25, center_y+25)
                case 3: # left
                    context.move_to(center_x-50, center_y)
                    context.line_to(center_x-25, center_y+25)
                    context.line_to(center_x-25, center_y-25)
            context.close_path()


            if action == best:
                context.fill_preserve()
                context.set_source_rgba(1, 0, 0)
                context.set_line_width(1)
                context.stroke()
            else:
                context.fill()

print(f'saved {fname}')

figure, axes = plt.subplots(1)
# if plt.subplots() or plt.subplots(1), axes is <AxesSubplot:>
# if plt.subplots(2), axes is array([<AxesSubplot:>, <AxesSubplot:>], dtype=object)

def compute_averages(values, window=1):
    accumulator = 0
    accumulated = []
    for (i,v) in enumerate(values):
        accumulator += v
        if i >= window:
            accumulator -= values[i-window]
        accumulated.append(accumulator)

    running_average = [v / min(i+1, window) for i,v in enumerate(accumulated)]
    return running_average

y_values = compute_average(result['rewards_per_episode'])
x_values = list(range(len(y_values)))
axes.plot(x_values, y_values)

axes.set_title('')
axes.set_ylabel('Sum of rewards during episode')
axes.set_xlabel('episodes')
axes.xaxis.grid()
axes.yaxis.grid()
axes.set_ylim(bottom=-200, top=0)

figure.set_figwidth(12.8)
figure.set_figheight(4.8)
#figure.legend(labels)
fname = 'plot.svg'
figure.savefig('plot.svg', format='svg', dpi=1200, bbox_inches='tight')
print(f'saved {fname}')


