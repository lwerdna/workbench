#!/usr/bin/env python

import math
import json

width=500
height=500

# where:
#	lon in degrees, range [-180, 180]
#	lat in degrees, range [-90, 90]
# returns:
#	x in range [0,width-1]
#   y in range [0,height-1]
def mercator(lon, lat):
	global width, height

	# 
	y = 0
	x = (lon+180)/360.0 * width

	tmp = abs(lat) * (math.pi/180)
	tmp = math.log( math.tan(math.pi/4 + tmp/2) )

	# clamp the output
	# as input latitude approaches 90 degrees (pi/2), the output is nearly a vertical asymptote
	if tmp >= 2*math.pi:
		if lat < 0:
			y = 0
		else:
			y = height-1
	else:
		if lat < 0:
			y = height/2 - tmp/(2*math.pi) * (height/2)
		else:
			y = height/2 + tmp/(2*math.pi) * (height/2)

	return (x, y)

jsobj = None
with open('earth-coastlines-10km.geo.json') as fp:
	jsobj = json.load(fp)

print dir(jsobj)
print jsobj.keys()

assert jsobj['type'] == 'GeometryCollection'
gc = jsobj['geometries']

mp = gc[0]
assert mp['type'] == 'MultiPolygon'

fp = open('mercator.svg', 'w')
fp.write('<svg width="%f" height="%f" xmlns="http://www.w3.org/2000/svg">\n' % (width,height))

(lathi,latlo) = (0,1000)
(yhi,ylo) = (0,1000)

for polygon in (mp['coordinates']):
	print 'polygon is: ', polygon
	points = polygon[0]

	fp.write('<polyline points="')
	for (lon,lat) in points:
		lathi = max(lathi, lat)
		latlo = min(latlo, lat)

		# lat/lon -> Cartesian in NE quadrant
		(x,y) = mercator(lon, lat)
		yhi = max(yhi, y)
		ylo = min(ylo, y)
		# Cartesian to SVG, where y axis grows downward
		y = height - y

		fp.write('%f,%f ' % (x,y))

	fp.write('" style="fill:none;stroke:black;stroke-width:.1" />\n')

# red rectangles every 5 degrees
tracers = []
for lat in xrange(-85,90,5):
	for lon in xrange(-175,180,5):
		(x0,y0) = mercator(lon, lat)
		(x1,y1) = mercator(lon+1, lat)
		(x2,y2) = mercator(lon+1, lat+1)
		(x3,y3) = mercator(lon, lat+1)
		y = height - y
		fp.write('<polyline points="%f,%f %f,%f %f,%f %f,%f, %f,%f" style="fill:none;stroke:red;stroke-width:.1" />\n' % \
			(x0,y0,x1,y1,x2,y2,x3,y3,x0,y0))

fp.write('</svg>\n')

print 'lathi: ', lathi
print 'latlo: ', latlo
print 'yhi: ', yhi
print 'ylo: ', ylo
