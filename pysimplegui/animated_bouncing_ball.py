#!/usr/bin/env python

# PIL image to PySimpleGUI Image via base64 string

import io
import base64
from PIL import Image, ImageDraw
import PySimpleGUI as sg

width = 320
height = 240

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
	x = 3
	y = 5
	delta_x = 2 
	delta_y = 3
	img = Image.new('RGB', (width, height))
	draw = ImageDraw.Draw(img)

	# create Tk-compatible image	
	imgtk = img_to_b64gif(img)

	sgImage = sg.Image(data=imgtk, size=(width, height))
	gui_rows = [[sg.Quit()],
				[sgImage]
				]  
	  
	window = sg.Window('Animated Bouncing Ball', auto_size_text=True).Layout(gui_rows)  
	 
	# service events
	while 1:
		#print('calling window.Read()')
		event, valuesDict = window.Read(timeout=10)  
		if event == None:
			print('None event')
			break
		elif event == '__TIMEOUT__':
			draw.rectangle((0,0,width,height), fill='black', outline='black')
			draw.ellipse((x, y, x+20, y+20), fill = 'blue', outline ='blue')	
			draw.text((5,5), "(x,y) = (%d,%d)" % (x,y))
			x += delta_x
			y += delta_y
			if x+20 > width or x < 0: delta_x *= -1
			if y+20 > height or y < 0: delta_y *= -1
	
			sgImage.Update(data=img_to_b64gif(img))

		elif event == 'Quit':
			print('Quit event')
			break
		elif event == 'Forward':
			print('FORWARD!')
		else:
			print('unknown event: ', event)
			break
 
	window.Close()
