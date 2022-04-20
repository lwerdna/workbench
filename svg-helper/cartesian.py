#!/usr/bin/env python

from helper import *

length = 640
px_per_unit = length / 10

d = Drawing(640, 640, transform=lambda x,y: (320+64*x, 320-64*y))

d.guide(10,10)
d.arrow(0,0, 3,3)
d.double_arrow(-5,0, 5,0)
d.export_svg('/tmp/tmp.svg')

