#!/usr/bin/env python

import re
from bs4 import BeautifulSoup

def parse(fpath):
	with open(fpath) as fp:
		html = fp.read()

	soup = BeautifulSoup(html, 'html.parser')

	for div in soup.find_all('div', 'intrinsic'):
		for label in div.find_all('label'):
			tmp = label.get_text().strip()
			tmp = tmp[0:tmp.index(')')+1]
			print(tmp, end='')
			#print(re.match(r'.*     (.*)<span.*', str(label)).group(1), label)
		for pre in div.find_all('pre'):
			print('; // ' + pre.get_text().strip())
			break

for i in range(1, 146+1):
	#print('// parsing %d.html' % i)
	parse('./html/%d.html' % i)
