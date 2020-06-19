#!/usr/bin/env python

import re
import sys

fin = sys.argv[1]

with open(fin) as fp:
	lines = [x.rstrip() for x in fp.readlines()]

for line in lines:
	m = re.match(r'^<!-- EMBED:(.*) -->', line)
	if not m:
		print(line)
		continue

	with open(m.group(1)) as fp:
		print(fp.read())

