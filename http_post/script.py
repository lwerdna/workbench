#!/usr/bin/env python

import cgi

form = cgi.FieldStorage();

path = form['path'].value
resp += 'using path: %s\n' % path
fname = form['fname'].value
resp += 'using file name: %s\n' % fname
fdata = form['fdata'].value
resp += 'using file data: %s...%s (%d chars)\n' % \
	(fdata[0:4], fdata[-4:], len(fdata))

os.chdir(path)
fp = open(fname, 'wb')
fp.write(base64.b64decode(fdata))
fp.close()

