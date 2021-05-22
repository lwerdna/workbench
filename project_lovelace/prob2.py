#!/usr/bin/env python

import math

c = 299792458

# Int (meters) -> Float (seconds)
def light_time(distance):
	global c
	return distance / c

if __name__ == '__main__':
	assert math.isclose(light_time(376291900), 1.255175, rel_tol=.01)
	assert math.isclose(light_time(299792458), 1.0, rel_tol=.01)

