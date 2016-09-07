#!/usr/bin/env python

import os
import sys

from PIL import Image, ImageDraw, ImageFont

#import pdb
#pdb.set_trace()

ifile = sys.argv[1]
cfile = sys.argv[2]

fp = open(ifile, 'r')
ilines = fp.readlines()
fp.close()

fp = open(cfile, 'r')
clines = fp.readlines()
fp.close()

img = Image.new('RGB', (256,256))
draw = ImageDraw.Draw(img)

# todo: look up ascent and descent
#fontMono = ImageFont.truetype("FreeMonoBold.ttf", 14)
#fontMono = ImageFont.truetype("PerfectDosVga437.ttf", 14)
fontMono = ImageFont.truetype("clacon.ttf", 26)
(charWidth,charHeight) = draw.textsize("X",font=fontMono)
print "(charWidth,charHeight)=(%d,%d)" % (charWidth,charHeight)

(imageWidth,imageHeight)=(0,0)
imageHeight = charHeight * len(ilines)
imageWidth = charWidth * max(map(len, ilines))
print "(imageWidth,imageHeight)=(%d,%d)" % (imageWidth,imageHeight)

img = Image.new('RGB', (imageWidth,imageHeight))
draw = ImageDraw.Draw(img)

(x,y)=(0,0)
for i in range(len(ilines)):
	iline = ilines[i]
	#cline = clines[i]

	ichars = list(iline)
	#cchars = list(cline)

	for c in ichars:
		#print "drawing at (%d,%d)" % (x,y)
		p0 = x*charWidth
		p1 = y*charHeight
		draw.rectangle((p0,p1,p0+charWidth,p1+charHeight),fill=(0,0,255))
		draw.text((x*charWidth,y*charHeight), c, fill=(0,255,255), font=fontMono)	
		x += 1

	x = 0
	y += 1

img.show()			
