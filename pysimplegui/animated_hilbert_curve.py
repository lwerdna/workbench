#!/usr/bin/env python

# PIL image to PySimpleGUI Image via base64 string

import io
import base64
from PIL import Image, ImageDraw
import PySimpleGUI as sg

n = 64
width = 4*n
height = 4*n

#------------------------------------------------------------------------------

def rot(n, x, y, rx, ry):
	if ry == 0:
		if rx == 1:
			x = n-1 - x;
			y = n-1 - y;

		(y,x) = (x,y)

	return (x,y)

def d2xy(n, d):
	(x,y,t) = (0,0,d)

	s = 1
	while s<n:
		rx = 1 & (t//2)
		ry = 1 & (t ^ rx)
		(x, y) = rot(s, x, y, rx, ry)
		x += s * rx
		y += s * ry
		t = t//4
		s *= 2

	return (x,y)

#------------------------------------------------------------------------------

def img_to_b64gif(img):
	# PIL -> gif -> string
	gif = None
	with io.BytesIO() as output:
		img.save(output, format="GIF")
		gif = output.getvalue()

	# gif string -> base64
	return base64.b64encode(gif)

if __name__ == '__main__':
	# drawing state
	dlimit = 0
	points = []
	img = Image.new('RGB', (width, height))
	draw = ImageDraw.Draw(img)

	# create Tk-compatible image	
	imgtk = img_to_b64gif(img)

	sgImage = sg.Image(data=imgtk, size=(width, height))
	gui_rows = [[sg.Quit()],
				[sgImage]
				]  
	  
	window = sg.Window('Animated Hilbert Draw', auto_size_text=True).Layout(gui_rows)  
	 
	# service events
	while 1:
		#print('calling window.Read()')
		event, valuesDict = window.Read(timeout=10)  
		if event == None:
			print('None event')
			break
		elif event == '__TIMEOUT__':
			if dlimit >= n**2: continue

			points.append(d2xy(n**2, dlimit))
			if len(points) < 2: continue

			(x0,y0) = points[-2]
			(x1,y1) = points[-1]
			(x0,y0,x1,y1) = map(lambda a: 4*a+1, (x0,y0,x1,y1))
			draw.line((x0,y0, x1,y1), width=1, fill="#ff0000")
	
			sgImage.Update(data=img_to_b64gif(img))
			
			dlimit += 1

		elif event == 'Quit':
			print('Quit event')
			break
		elif event == 'Forward':
			print('FORWARD!')
		else:
			print('unknown event: ', event)
			break
 
	window.Close()
