#!/usr/bin/env python

import sys
from math import sin, cos, pi, sqrt

vertices = []

# this is a direct port of Build_Shape() from gouraudshade-0.1-Linux.zip src/main.cc
# http://insolitdust.sourceforge.net/code.html
def Build_Shape():
	Shape = []

	# defines
	SCALING_FACTOR1 = 10
	SCALING_FACTOR2 = 50
	RADIUS1 = 25
	RADIUS2 = 50
	RADIUS3 = 25

	#for(Alpha = 0, Count2 = 0; Count2 < SCALING_FACTOR2; Count2++, Alpha += 2 * pi / SCALING_FACTOR2)
	Alpha = 0
	Count2 = 0
	while Count2 < SCALING_FACTOR2:
		X = RADIUS2 * cos(2 * Alpha) + RADIUS1 * sin(Alpha);
		Y = RADIUS2 * sin(2 * Alpha) + RADIUS1 * cos(Alpha);
		Z = RADIUS2 * cos(3 * Alpha);
		dx = -2 * RADIUS2 * sin(2 * Alpha) + RADIUS1 * cos(Alpha);
		dy = 2 * RADIUS2 * cos(2 * Alpha) - RADIUS1 * sin(Alpha);
		dz = -3 * RADIUS2 * sin(3 * Alpha);
		Value = sqrt(dx * dx + dz * dz);
		Modulus = sqrt(dx * dx + dy * dy + dz * dz);

		#for(Beta = 0, Count1 = 0; Count1 < SCALING_FACTOR1; Count1++, Beta += 2 * pi / SCALING_FACTOR1)
		Beta = 0
		Count1 = 0
		while Count1 < SCALING_FACTOR1:
			Shape.append((
				X - RADIUS3 * (cos(Beta) * dz - sin(Beta) *	dx * dy / Modulus) / Value,
				Y - RADIUS3 * sin(Beta) * Value / Modulus,
				Z + RADIUS3 * (cos(Beta) * dx + sin(Beta) * dy * dz / Modulus) / Value
			))

			Count1 += 1
			Beta += 2*pi/SCALING_FACTOR1

		Count2 += 1
		Alpha += 2*pi/SCALING_FACTOR2

	return Shape

vertices = Build_Shape()
sys.stdout.write('points = [\n')
for i in range(len(vertices)):
	if i%4 == 0: sys.stdout.write('\t')
	strs = map(lambda x: ('%.2f'%x).rjust(6), vertices[i])
	sys.stdout.write(','.join(strs))
	if i != len(vertices)-1: sys.stdout.write(', ')
	if (i+1)%4 == 0: sys.stdout.write('\n')
sys.stdout.write(']\n\n')

nsides = 11
npoints = len(vertices)
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

