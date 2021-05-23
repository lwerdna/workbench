#!/usr/bin/env python

import math

a = 2.757
b = 16.793

# Float (latitude) -> Float (kg)
def moose_body_mass(latitude):
    global a,b
    return a*latitude + b

if __name__ == '__main__':
    assert math.isclose(moose_body_mass(60.5), 183.5915)

