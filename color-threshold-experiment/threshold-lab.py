#!/usr/bin/env python

import io
import sys
import base64
from PIL import Image
import PySimpleGUI as sg

struct_elem = [	(-1,-1),(0,-1),(1,-1),
				(-1, 0),(0, 0),(1, 0),
				(-1, 1),(0, 1),(1, 1)	]

struct_elem = [			(0,-1),
				(-1, 0),(0, 0),(1, 0),
						(0, 1),			]

#------------------------------------------------------------------------------
# PIL, framebuf stuff
#------------------------------------------------------------------------------
def framebuf_to_tk(fb, w, h):
	# create PIL image
	img = Image.new('RGB', (w, h))
	px = img.load()

	# copy framebuf to PIL image
	# TODO: use frombytes() or frombuffer()
	for y in range(h):
		for x in range(w):
			px[x,y] = fb[y*w + x]

	# PIL -> gif -> string
	gif = None
	with io.BytesIO() as output:
		img.save(output, format="GIF")
		gif = output.getvalue()

	# gif string -> base64
	return base64.b64encode(gif)

def pil_to_framebuf(img):
	data = list(img.tobytes())

	# if 4 bytes per pixel, assume RGB
	if len(data) == img.width*img.height*4:
		return [tuple(data[p:p+3]) for p in range(0,len(data),4)]
	# if 3 bytes per pixel, assume RGB
	elif len(data) == img.width*img.height*3:
		return [tuple(data[p:p+3]) for p in range(0,len(data),3)]
	#
	else:
		raise Exception('unknown image format')

#------------------------------------------------------------------------------
# image processing
#------------------------------------------------------------------------------

# data: list of (r,g,b) tuples each in range [0,255]
def black_white(data, w, h, weights=(.3,.59,.11)):
	result = [None]*w*h

	for y in range(h):
		for x in range(w):
			coord = y*w + x
			(r,g,b) = data[coord]
			luminosity = int(weights[0]*r + weights[1]*g + weights[2]*b)
			result[coord] = (luminosity, luminosity, luminosity)

	return result

# data: list of (r,g,b) tuples each in range [0,255]
# thresh: percentage value [0,100] over which luminosity should go white
def threshold(data, w, h, thresh):
	result = black_white(data, w, h)

	for y in range(h):
		for x in range(w):
			coord = y*w + x
			(r,g,b) = data[coord]
			if 100*(r/255.0) > thresh:
				result[coord] = (255,255,255)
			else:
				result[coord] = (0,0,0)

	return result

def color_map(fb, w, h):
	result = [None]*w*h

	for k in xrange(w*h):
		p = fb[k]
		if p==(255,0,0): p=(255,84,126)
		elif p==(0,255,0): p=(5,255,161)
		elif p==(0,0,255): p=(195,96,255)
		elif p==(255,255,0): p=(112,76,232)
		elif p==(0,255,255): p=(93,119,225)
		elif p==(255,0,255): p=(232,76,227)
		elif p==(255,255,255): p=(255,255,255)
		elif p==(0,0,0): p=(0,0,0)
		result[k] = p

	return result

def threshold_rgb(data, w, h, thresh):
	result = [None]*w*h

	thresh = (thresh/100.0)*255

	for y in range(h):
		for x in range(w):
			coord = y*w + x
			(r,g,b) = data[coord]

			r = [0,255][r>thresh]
			g = [0,255][g>thresh]
			b = [0,255][b>thresh]

			result[coord] = (r,g,b)

	return result;

# data: list of (r,g,b) tuples each in range [0,255]
# struct_elem: list of (dx,dy) displacement tuples
def dilate(data, w, h, struct_elem):
	result = [None]*w*h

	for y in range(h):
		for x in range(w):
			idx = y*w + x

			checks = map(lambda p: (x+p[0], y+p[1]), struct_elem)

			# by default result pixel is white
			wpix = (255,255,255)
			# if any black pixel in structure element, set black
			for (cx,cy) in checks:
				idx2 = cy*w + cx

				if idx2>=0 and idx2<(w*h) and data[idx2] == (0,0,0):
					wpix = (0,0,0)
					break

			result[idx] = wpix

	return result

#------------------------------------------------------------------------------
# main
#------------------------------------------------------------------------------

if __name__ == '__main__':
	# input image to framebuf
	print("opening %s\n" % sys.argv[1])
	img_pil = Image.open(sys.argv[1])
	(w,h) = (img_pil.width, img_pil.height)
	print('width/height: %d/%d' % (w,h))
	framebuf = pil_to_framebuf(img_pil)

	# framebuf to Tk image (gif)
	img_tk = framebuf_to_tk(framebuf, w, h)

	# simplegui image widget
	sgImage = sg.Image(data=img_tk, size=(w,h))

	layout = [
		[sg.Text("Threshold:"), sg.Slider(range=(0,100), orientation='h', default_value=50, key="_THRESH_")],
		[sgImage]
	]

	window = sg.Window('Threshold Experiments', auto_size_text=True).Layout(layout)

	while (True):  
		# This is the code that reads and updates your window  
		event, values = window.Read(timeout=100)  
		if event == None:
			print('None event')
			break
		elif event == '__TIMEOUT__':
			#print('TIMEOUT event')
			pass
		elif event == 'Quit':
			print('Quit event')
			break
		elif event == 'Forward':
			print('FORWARD!')
		else:
			print('unknown event: ', event)

		print('values: ', values)

		thresh = values['_THRESH_']

		# framebuf -> (processing) -> framebuf2
		fb2 = threshold_rgb(framebuf, w, h, thresh)
		#fb2 = dilate(fb2, w, h, struct_elem)
		#fb2 = color_map(fb2, w, h)
		# framebuf -> Tk image
		img_tk = framebuf_to_tk(fb2, w, h)
		#
		sgImage.Update(data=img_tk)

	window.Close()
