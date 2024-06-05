#!/usr/bin/env python

import re
import sys
from bs4 import BeautifulSoup

def parse(fpath):
	with open(fpath) as fp:
		html = fp.read()

	soup = BeautifulSoup(html, 'html.parser')
	for br in soup('br'):
		br.replace_with('\n')

	for div in soup.find_all('div', 'intrinsic'):
		for label in div.find_all('label'):
			tmp = label.get_text().strip()
			tmp = tmp[0:tmp.index(')')+1]
			tmp = tmp.replace('\xa0', '')
			print('FSIG: %s' % tmp)
			#print(re.match(r'.*     (.*)<span.*', str(label)).group(1), label)
		pres = [pre.get_text() for pre in div.find_all('pre')]
		#pres = [pre.replace(b'\xe2\x86\x92', b'->') for pre in pres]
		asig = pres[0].strip()
		print('ASIG: %s' % asig)
		arg_prep = pres[1]
		arg_prep = arg_prep.replace('→', '->')
		print('ARGPREP:')
		for ap in arg_prep.split('\n'):
			if not ap or ap.isspace(): continue
			print('\t%s' % ap)
		results = pres[2]
		results = results.replace('→', '->')
		print('RESULTS:')
		for ap in results.split('\n'):
			if not ap or ap.isspace(): continue
			print('\t%s' % ap)
		print()

for i in range(1, 146+1):
	print('// parsing %d.html' % i)
	parse('./html/%d.html' % i)
