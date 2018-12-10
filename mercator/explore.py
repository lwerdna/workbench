#!/usr/bin/env python

import json

jsobj = None
with open('earth-coastlines-10km.geo.json') as fp:
	jsobj = json.load(fp)

print dir(jsobj)
print jsobj.keys()

assert jsobj['type'] == 'GeometryCollection'
gc = jsobj['geometries']

mp = gc[0]
assert mp['type'] == 'MultiPolygon'

xlo,xhi,ylo,yhi=(0,0,0,0)

for (i,polygon) in enumerate(mp['coordinates']):
	points = polygon[0]
	print 'polygon %d has %d points' % (i, len(points))

	for point in points:
		print 'on point: ' + str(point)
		xlo = min(xlo, point[0])
		xhi = max(xhi, point[0])
		ylo = min(ylo, point[1])
		yhi = max(yhi, point[1])

print 'x goes from [%f,%f]' % (xlo,xhi)
print 'y goes from [%f,%f]' % (ylo,yhi)

