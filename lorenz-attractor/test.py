#!/usr/bin/env python

#x, y, z = 0, 0, 0
x, y, z = 0, 1, 1.5

def lorenz_system(dt, params, start):
    x, y, z = start
    rho, sigma, beta = params
    while True:
        x += sigma * (y-x) * dt
        y += (x * (rho - z) - y) * dt
        z += (x * y - beta*z) * dt
        yield (x,y,z)

# starting point does matter! (0,0,0) is stuck
ls = lorenz_system(.001, (28,10,8/3), (0,0,0))
assert next(ls) == next(ls)

# find rough bounds of x,y,z
# result:
# x:[-19.14084857304701, 19.562962854301762]
# y:[-26.29887460797714, 27.117164150680512]
# z:[0, 47.78857432451132]
if 0:
    dt = .001
    duration = 1000
    ls = lorenz_system(dt, (28,10,8/3), (0,1,1.5))
    x_hi, x_lo, y_hi, y_lo, z_hi, z_lo = 0, 0, 0, 0, 0, 0
    for i in range(int(duration/dt)):
        x,y,z = next(ls)
        x_hi = max(x, x_hi);
        x_lo = min(x, x_lo);
        y_hi = max(y, y_hi);
        y_lo = min(y, y_lo);
        z_hi = max(z, z_hi);
        z_lo = min(z, z_lo);
    print(f'x:[{x_lo}, {x_hi}]')
    print(f'y:[{y_lo}, {y_hi}]')
    print(f'z:[{z_lo}, {z_hi}]')

xs, ys, zs = [], [], []
dt = .001
duration = 100
ls = lorenz_system(dt, (28,10,8/3), (0,1,1.5))
for i in range(int(duration/dt)):
    x,y,z = next(ls)
    xs.append(x)
    ys.append(y)
    zs.append(z)

import matplotlib.pyplot as plt
ax = plt.figure().add_subplot(projection='3d')
ax.plot(xs, ys, zs, lw=0.5)
ax.set_xlabel("X Axis")
ax.set_ylabel("Y Axis")
ax.set_zlabel("Z Axis")
ax.set_title("Lorenz Attractor")
plt.show()

