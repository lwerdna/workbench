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

fp = open('test.svg', 'w')

fp.write('<svg width="%f" height="%f" xmlns="http://www.w3.org/2000/svg">\n' % (360, 180))

for (i,polygon) in enumerate(mp['coordinates']):
	points = polygon[0]

	fp.write('<!-- polygon #%d -->' % i)
	fp.write('<polyline points="')
	for (lon,lat) in points:
		# lat/long -> Cartesian
		# very naive "flattening" map
		(x,y) = (lon, lat)

		# shift image to positive Cartesian quadrant
		# [-180,180]->[0,360], [-90,90]->[0,180]
		(x,y) = (x+180, y+90)

		# Cartesian to SVG, where y axis grows downward
		y = 180-y

		fp.write('%f,%f ' % (x,y))

	fp.write('" style="fill:none;stroke:black;stroke-width:.1" />\n')

fp.write('</svg>\n')

