#!/usr/bin/env python

import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, LinearSegmentedColormap

cmap_names = [
'viridis', 'plasma', 'inferno', 'magma', 'cividis',
'Greys', 'Purples', 'Blues', 'Greens', 'Oranges', 'Reds',
'YlOrBr', 'YlOrRd', 'OrRd', 'PuRd', 'RdPu', 'BuPu',
'GnBu', 'PuBu', 'YlGnBu', 'PuBuGn', 'BuGn', 'YlGn',
'binary', 'gist_yarg', 'gist_gray', 'gray', 'bone', 'pink',
'spring', 'summer', 'autumn', 'winter', 'cool', 'Wistia',
'hot', 'afmhot', 'gist_heat', 'copper',
'PiYG', 'PRGn', 'BrBG', 'PuOr', 'RdGy', 'RdBu',
'RdYlBu', 'RdYlGn', 'Spectral', 'coolwarm', 'bwr', 'seismic',
'twilight', 'twilight_shifted', 'hsv',
'Pastel1', 'Pastel2', 'Paired', 'Accent',
'Dark2', 'Set1', 'Set2', 'Set3',
'tab10', 'tab20', 'tab20b', 'tab20c',
'flag', 'prism', 'ocean', 'gist_earth', 'terrain', 'gist_stern',
'gnuplot', 'gnuplot2', 'CMRmap', 'cubehelix', 'brg',
'gist_rainbow', 'rainbow', 'jet', 'nipy_spectral', 'gist_ncar'
]

print('''
<!DOCTYPE html>
<html>
<head>
  <title>matplotlib colormaps in 256-entry arrays</title>
  <style>
  </style>
</head>
<body>

<h2>This is all the matplotlib palettes in arrays of 256 rgb codes. View the source to see the rgb codes in the comments.</h2>

''')

for name in cmap_names:
	cmap = plt.get_cmap(name)
	rgbas = cmap([1/256.0 * x for x in range(256)])
	assert len(rgbas) == 256

	htmls = []
	print('<h3>%s</h3>' % name)
	for (i,(r,g,b,a)) in enumerate(rgbas):
		assert a==1
		(r,g,b) = map(lambda x: int(x*255), [r,g,b])
		html = '#%02X%02X%02X' % (r,g,b)
		htmls.append(html)
	print('<!--', ','.join(htmls), '-->')
	for (i,html) in enumerate(htmls):
		if i%4 == 0:
			print('<span style="color:%s">&#9608;</span>' % html, end='')
	print('\n')

print('''
</body>
</html>
''')

