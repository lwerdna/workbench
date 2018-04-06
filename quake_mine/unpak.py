#!/usr/bin/env python

import os
import sys
from struct import pack, unpack

def dump_file(path, fp, offset, size):
	print 'dumping [0x%08X, 0x%08X) to %s' % \
	  (offset, offset+size, name)

	dirname = os.path.dirname(path)
	if dirname and not os.path.exists(dirname):
		os.makedirs(dirname)

	tmp = fp.tell()
	fp.seek(offset)
	with open(path, 'wb') as fp2:
		fp2.write(fp.read(size))
	fp.seek(tmp)

###############################################################################
# "main"
###############################################################################

if __name__ == '__main__':
	fpath = sys.argv[1]
	fp = open(fpath, "rb")

	assert fp.read(4) == 'PACK'

	(offset, size) = unpack('<II', fp.read(8))

	# loop over file table entries
	numFiles = size / 64
	fp.seek(offset)
	for i in range(numFiles):
		name = fp.read(56)
		name = name[0:name.index('\x00')]
		(offset, size) = unpack('<II', fp.read(8))
		dump_file(name, fp, offset, size)
	
	fp.close()
	sys.exit(0)

