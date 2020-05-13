#!/usr/bin/env python

import sys
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, LinearSegmentedColormap

cmap_names = [
'viridis', 'plasma', 'inferno', 'magma', 'cividis', 'Greys', 'Purples',
'Blues', 'Greens', 'Oranges', 'Reds', 'YlOrBr', 'YlOrRd', 'OrRd', 'PuRd',
'RdPu', 'BuPu', 'GnBu', 'PuBu', 'YlGnBu', 'PuBuGn', 'BuGn', 'YlGn', 'binary',
'gist_yarg', 'gist_gray', 'gray', 'bone', 'pink', 'spring', 'summer', 'autumn',
'winter', 'cool', 'Wistia', 'hot', 'afmhot', 'gist_heat', 'copper', 'PiYG',
'PRGn', 'BrBG', 'PuOr', 'RdGy', 'RdBu', 'RdYlBu', 'RdYlGn', 'Spectral',
'coolwarm', 'bwr', 'seismic', 'twilight', 'twilight_shifted', 'hsv', 'Pastel1',
'Pastel2', 'Paired', 'Accent', 'Dark2', 'Set1', 'Set2', 'Set3', 'tab10',
'tab20', 'tab20b', 'tab20c', 'flag', 'prism', 'ocean', 'gist_earth', 'terrain',
'gist_stern', 'gnuplot', 'gnuplot2', 'CMRmap', 'cubehelix', 'brg',
'gist_rainbow', 'rainbow', 'jet', 'nipy_spectral', 'gist_ncar'
]

for name in cmap_names:
	cmap = plt.get_cmap(name)
	rgbas = cmap([1/256.0 * x for x in range(256)])
	assert len(rgbas) == 256

	print('palette_%s = [' % name)
	colors = []
	for (i,(r,g,b,a)) in enumerate(rgbas):
		assert a==1
		(r,g,b) = map(lambda x: int(x*255), [r,g,b])
		color = '(0x%02X,0x%02X,0x%02X)' % (r,g,b)
		colors.append(color)
	lines = [','.join(colors[k:k+4]) for k in range(0,256,4)]
	print(',\n'.join(lines))
	print(']')

