#!/usr/bin/env python

import matplotlib
import matplotlib.pyplot as plt
plt.style.use('seaborn-whitegrid')

import numpy as np

if __name__ == '__main__':
    data = []

    fig, ax = plt.subplots(2)
    #ax[0].set_xlabel('input')
    #ax[0].set_ylabel('scalar')

    # do function
    # f(x) = x^3 + 4x^2 + 3x - 1
    x = np.linspace(-4, 2, 1000)
    y = x**3 + 4*x**2 + 3*x - 1
    ax[0].plot(x, y)

    # do gradient
    # f'(x) = 3x^2 + 8x + 3
    x_pos = []
    y_pos = []
    x_direct = []
    y_direct = []

    y = 0
    for x in [-4, -3.5, -3, -2.5, -2, -1.5, -1, -.5, 0, .5, 1, 1.5, 2]:
        x_pos.append(x)
        y_pos.append(0)

        x_direct.append(3*x*x + 8*x + 3)
        y_direct.append(0)

    # scale everything so biggest arrow is 1
    m = max([abs(x) for x in x_direct])
    #print('x_direct: ', x_direct)
    x_direct = [x/m for x in x_direct]
    #print('x_direct: ', x_direct)

    ax[1].quiver(x_pos, y_pos, x_direct, y_direct)

    # save it all
    plt.savefig('dim1.png')
    plt.close(fig)

