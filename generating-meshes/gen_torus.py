#!/usr/bin/env python

import sys
from math import sin, cos, pi

nsides = 8 # number of sides of the polygon cross section
nsteps = 16 # number of extrusions of the cross sections
rdisc = 20 # radius of the discs
rtorus = 50 # radius of the torus

screen_width = 128
screen_height = 128

npoints = nsides*nsteps

def get_torus_point(i):
	# angle around the disc
	theta = 1.0*i/nsides * 2*pi
	# angle around the torus
	phi = theta/nsteps
	# three points
	x = (rtorus + rdisc*cos(theta)) * cos(phi)
	y = (rtorus + rdisc*cos(theta)) * sin(phi)
	z = rdisc*sin(theta)
	# done
	return (x,y,z)

vertices = []
for i in range(npoints):
	vertices.append(get_torus_point(i))

sys.stdout.write('points = [\n')
for i in range(len(vertices)):
	if i%4 == 0: sys.stdout.write('\t')
	strs = map(lambda x: ('%.2f'%x).rjust(6), vertices[i])
	sys.stdout.write(','.join(strs))
	if i != len(vertices)-1: sys.stdout.write(', ')
	if (i+1)%4 == 0: sys.stdout.write('\n')
sys.stdout.write(']\n\n')

triangles = []
for i in range(npoints):
	#   p_{i+nsides}---->p_i
	#            ^ \     |
	#            |  \    |
	#            |   \   |
	#            |    \  |
	#            |     \ V
	# p_{i+nsides+1}<---p_i+1

	#triangles.append((i, (i+1)%npoints, (i+nsides)%npoints))
	triangles.append(((i+nsides)%npoints, (i+1)%npoints, i))
	#triangles.append(((i+1)%npoints, (i+nsides+1)%npoints, (i+nsides)%npoints))
	triangles.append(((i+nsides)%npoints, (i+nsides+1)%npoints, (i+1)%npoints))

sys.stdout.write('triangles = [\n')
for i in range(len(triangles)):
	if i%8 == 0: sys.stdout.write('\t')
	strs = map(lambda x: ('%d'%x).rjust(3), triangles[i])
	sys.stdout.write(','.join(strs))
	if i != len(triangles)-1: sys.stdout.write(', ')
	if (i+1)%8 == 0: sys.stdout.write('\n')
sys.stdout.write(']\n')

