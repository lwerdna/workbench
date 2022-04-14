#!/usr/bin/env python3

import os
import subprocess
from cp437 import getImgLine, getImgString
from PIL import Image, ImageDraw

bgcolor = (255, 255, 255)
delay = 100 # in 100'ths of second
margin = 4

def setDelay(delay_):
	global delay
	delay = delay_

def setMargin(margin_):
	global margin
	margin = margin_

def write(framesTxt, fnameOut):
	global delay, margin, bgcolor

	# convert text frames -> image frames
	framesImg = []
	for f in framesTxt:
		framesImg.append(getImgString(f))

	# add margins
	tmp = []
	for fi in framesImg:
		(width, height) = fi.size
		imgMargin = Image.new('RGB', (width+2*margin, height+2*margin), bgcolor)
		imgMargin.paste(fi, (margin, margin))
		tmp.append(imgMargin)
	framesImg = tmp

	# map images frames -> file names
	framesFname = []
	for (i, img) in enumerate(framesImg):
		fname = 'frame%04d.png' % i
		print("writing %s" % fname)
		img.save(fname)
		framesFname.append(fname)
	
	# call imagemagick
	print("calling imagemagick")
	args = ['convert']
	args += ['-delay', '%d' % delay]
	args += ['-loop', '0']
	args += framesFname
	args.append(fnameOut)
	print("executing: ", args)
	subprocess.call(args)
	
	# delete temporary files
	for fname in framesFname:
		print("deleting %s" % fname)
		os.unlink(fname)

