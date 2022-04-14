#!/usr/bin/env python3

import sys
from cp437 import getImgLine
from PIL import Image, ImageDraw

if __name__ == '__main__':
	if not sys.argv[1:]:
		raise Exception('need one arg')

	imgOut = getImgLine(sys.argv[1])
	imgOut.save('argv1.png')
	print("wrote argv1.png")
