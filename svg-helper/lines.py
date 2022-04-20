#!/usr/bin/env python

from helper import *

d = Drawing(640, 480)
d.guide(40, 40)
d.line(200,200, 400,400)
d.arrow(250,200, 450,400)
d.double_arrow(300,200, 500,400)
d.line_segment(350,200, 550,400)
d.ray(400,200, 600,400)
d.export_svg('/tmp/tmp.svg')

