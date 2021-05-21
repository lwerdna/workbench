#!/usr/bin/env python

# TIL: math.isclose()

import math

def fahrenheit_to_celsius(F):
	return 5/9.0 * (F-32)

if __name__ == '__main__':
	assert math.isclose(fahrenheit_to_celsius(77.9), 25.5)
	assert math.isclose(fahrenheit_to_celsius(32), 0)

