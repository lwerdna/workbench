#!/usr/bin/env python

import pygame
from colormap import palette

width = 0x128
height = 0xc2
numpix = width*height

skin = ''
with open('./resource/ID1/progs/player.mdl', 'rb') as fp:
	skin = fp.read()[0x58:0x58+numpix]


pygame.init()
screen = pygame.display.set_mode((width, height))

done = False
while not done:
	for event in pygame.event.get():
		if event.type == pygame.QUIT:
			done = True

	for x in range(width):
		for y in range(height):
			pidx = ord(skin[y*width + x])
			(r,g,b) = palette[pidx]
			screen.set_at((x,y), (r,g,b,0xFF))

	pygame.display.flip()
