#!/usr/bin/env python

import math
import matplotlib
import matplotlib.pyplot as plt
from matplotlib import cm

import numpy as np


tx = np.linspace(-4, 4, 200)
ty = np.linspace(-4, 4, 200)
xx, yy = np.meshgrid(tx, ty)
tz = xx**3 - xx/4 + yy**3 + yy/7
fig = plt.figure()
ax = fig.add_subplot(1, 1, 1, projection='3d')
ax.set_xlabel('X')
ax.set_ylabel('Y')
ax.set_zlabel('Z')
ax.plot_surface(xx, yy, tz, cmap=cm.coolwarm)
plt.savefig('dim2_3d.png')

x_pos = []
y_pos = []
x_direct = []
y_direct = []
y = 0
for x in np.linspace(-4, 4, 20):
    for y in np.linspace(-4, 4, 20):
        x_pos.append(x)
        y_pos.append(y)
        x_direct.append(3*x*x - 1/4)
        y_direct.append(3*y*y + 1/7)

fig = plt.figure()
ax = fig.add_subplot(1, 1, 1)
ax.quiver(x_pos, y_pos, x_direct, y_direct)
plt.savefig('dim2_gradient.png')

# save it all
plt.close(fig)
