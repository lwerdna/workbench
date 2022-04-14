#!/usr/bin/env python3

import sys
from PIL import Image, ImageDraw

PX_WIDTH_CHAR = 8
PX_HEIGHT_CHAR = 19

# return the portion of the cp437 image for a char (greyscale)
#
def getImgCharRaw(c):
	imgFont = Image.open('cp437-19.png')

	# map byte [0,255] to row/col coords within 32x8 grid of characters
	o = ord(c)
	row = o // 32
	col = o % 32
	#print("accessing letter '%s' from (row,col)=(%d,%d)" % (c, row, col))
	# map 32x8 grid to pixel coords in 256x152
	x = PX_WIDTH_CHAR * col
	y = PX_HEIGHT_CHAR * row
	#print("accessing letter '%s' from (x,y)=(%d,%d)" % (c, x, y))
	# return image from pixel coords
	imgCrop = imgFont.crop((x, y, x+PX_WIDTH_CHAR, y+PX_HEIGHT_CHAR))
	#imgCrop.save(c + '.png')
	return imgCrop

# return an image for a character of text, optional colors
#
def getImgChar(c, colorFore=None, colorBack=None):
	imgChar = getImgCharRaw(c)			# pix are [0,255]
	imgChar = imgChar.convert('RGB')	# pix are ([0,255],[0,255],[0,255])

	pix = imgChar.load()

	(width, height) = imgChar.size

	# replace foreground and background colors if requested
	if colorFore or colorBack:
		for y in range(height):
			for x in range(width):
				if colorFore and pix[x,y] == (0,0,0):
					pix[x,y] = colorFore
				elif colorBack and pix[x,y] == (255,255,255):
					pix[x,y] = colorBack

	return imgChar

# return an image for a single line of text
#
def getImgLine(string, colorFore=None, colorBack=None):
	(width, height) = (len(string), 1)
	imgOut = Image.new('RGB', ((width * PX_WIDTH_CHAR, height * PX_HEIGHT_CHAR)))

	cursor = 0
	for c in string:
		imgChar = getImgChar(c, colorFore, colorBack)
		(x, y) = (cursor * PX_WIDTH_CHAR, 0)
		#print "drawing char '%s' at (%d,%d)" % (c, x, y)
		imgOut.paste(imgChar, (x, y))
		cursor += 1

	return imgOut

# return an image for (possible) multiple lines of text
#
def getImgString(string, colorFore=None, colorBack=None):
	lines = string.split('\n')
	maxLen = max(map(len, lines))
	(width, height) = (maxLen, len(lines))

	imgOut = Image.new('RGB', ((width * PX_WIDTH_CHAR, height * PX_HEIGHT_CHAR)))

	cursorY = 0
	for line in lines:
		line += ' '*(maxLen - len(line)) # pad
		imgLine = getImgLine(line, colorFore, colorBack)
		(x, y) = (0, cursorY * PX_HEIGHT_CHAR)
		#print "drawing line '%s' at (%d,%d)" % (line, x, y)
		imgOut.paste(imgLine, (x, y))
		cursorY += 1

	return imgOut

if __name__ == '__main__':
    import sys

    img = getImgLine('abcde')
    img.save('/tmp/abcde.png')
    sys.exit(-1)

    img = getImgCharRaw('a')
    img.save('/tmp/a.png')

    img = getImgChar('b')
    img.save('/tmp/b.png')

    img = getImgChar('c')
    img.save('/tmp/n.png')

    img = getImgChar('d')
    img.save('/tmp/n.png')

    sys.exit(-1)

    img = getImgCharRaw('f')
    img.save('/tmp/f.png')

    img = getImgLine('abn')
    img.save('/tmp/abn.png')

    img = getImgLine('abcdefghijklmnopqrstuvwxyz')
    img.save('/tmp/abcdefghijklmnopqrstuvwxyz.png')

