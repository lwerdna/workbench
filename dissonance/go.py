#!/usr/bin/env python

# https://music.stackexchange.com/questions/4439/is-there-a-way-to-measure-the-consonance-or-dissonance-of-a-chord
# from http://www.acousticslab.org/learnmoresra/moremodel.html

import sys
import math

fundamental = 440

def calculate_roughness(f1, f2, a1=1, a2=1):
	(a_min, a_max) = (min(a1, a2), max(a1, a2))
	(f_min, f_max) = (min(f1, f2), max(f1, f2))
	(b1, b2, s1, s2) = (3.5, 5.75, 0.0207, 18.96)
	s = .24 / (s1*f_min + s2)
	x = a_min * a_max
	y = 2 * a_min / (a_min + a_max)
	z = math.e**(-b1*s*(f_max-f_min)) - math.e**(-b2*s*(f_max-f_min))
	return x**.1 * .5*(y**3.11) * z

# roughness with roughness of overtones
def calculate_dissonance(f1, f2, a1=1, a2=1):
	# amplitude falls at rate .88
	overtones1 = [(f1,1), (2*f1,.88), (3*f1,.77), (4*f1,.68), (5*f1,.60), (6*f1,.53), (7*f1,.41), (8*f1,.36)]
	overtones2 = [(f2,1), (2*f2,.88), (3*f2,.77), (4*f2,.68), (5*f2,.60), (6*f2,.53), (7*f2,.41), (8*f2,.36)]
	r = 0;
	for i in range(8):
		for j in range(8):
			(f1,a1) = overtones1[i]
			(f2,a2) = overtones2[j]
			r += calculate_roughness(f1, f2, a1, a2)
	return r

note_names = ['C ', 'C#', 'D ', 'D#', 'E ', 'F ', 'F#', 'G ', 'G#', 'A ', 'A#', 'B ', 'C ']

#tet_root = 2**(1/12)
#base_freq = fundamental
#for e in range(13):
#	freq = base_freq * tet_root**e
#	roughness = calculate_roughness(base_freq, freq)
#	print('C (%.2fhz) and %s (%.2fhz) have roughness: %f' % \
#		(base_freq, note_names[e], freq, roughness))

if sys.argv[1:] and sys.argv[1] in ['rough', 'roughness']:
	for freq in [(1 + (x/500)) * fundamental for x in range(500+1)]:
		r = calculate_roughness(fundamental, freq)
		print('%f %f' % (freq, r))

else:
	for freq in [(1 + (x/500)) * fundamental for x in range(500+1)]:
		r = calculate_dissonance(fundamental, freq)
		print('%f %f' % (freq, r))
	
