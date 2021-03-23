#!/usr/bin/env python
#
# example usage:
# ./scrape.py https://www.floridagofishing.com/reefs/ce-reefs-brevard-county.html

import os
import re
import sys

from bs4 import BeautifulSoup

from subprocess import Popen, PIPE
def shellout(cmd):
	process = Popen(cmd, stdout=PIPE, stderr=PIPE)
	(stdout, stderr) = process.communicate()
	stdout = stdout.decode("utf-8")
	stderr = stderr.decode("utf-8")
	process.wait()
	return (stdout, stderr)

if __name__ == '__main__':
	url = sys.argv[1]
	#print('url: %s' % url)
	fname = re.match(r'^.*/(.*\.html)$', url).group(1)
	#print('fname: %s' % fname)

	if os.path.exists(fname):
		#print('cached!')
		pass
	else:
		cmd = ['wget', '--user-agent="Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; SV1)"', url]
		#print('cmd: %s' % cmd)
		shellout(cmd)

	#print('opening %s' % fname)
	html_doc = open(fname).read()
	soup = BeautifulSoup(html_doc, 'html.parser')

	div = soup.find(id='yuidatatable')
	table = div.find('table')
	first = True
	for tr in table.find_all('tr'):
		if first:
			cells = tr.find_all('th')
			first = False
		else:
			cells = tr.find_all('td')
		
		assert len(cells) == 6
		cells = [x.text.replace(',', ' ') for x in cells]
		cells = ['' if re.match(r'^\s+$', x) else x for x in cells]
		line = ','.join(cells)
		if re.match(r'^[,\s]+$', line):
			continue
		print('%s' % line)

