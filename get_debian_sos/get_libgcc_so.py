#!/usr/bin/env python

# download debian shared objects, separate debug symbols, and unstrip them

import os, sys, re

from subprocess import Popen, PIPE
def shellout(cmd):
	process = Popen(cmd, stdout=PIPE, stderr=PIPE)
	(stdout, stderr) = process.communicate()
	stdout = stdout.decode("utf-8")
	stderr = stderr.decode("utf-8")
	process.wait()
	return (stdout, stderr)

def get_files(ext=''):
	return sum([[os.path.join(r, f) for f in
		[f for f in fs if f.endswith(ext)]]
		for (r,d,fs) in os.walk('.')], [])

if __name__ == '__main__':
	if sys.argv[1] == 'fetch':
		fnames = [
			'libgcc1-dbg_6.3.0-18+deb9u1_amd64.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_arm64.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_armel.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_armhf.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_i386.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_mips.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_mips64el.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_mipsel.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_ppc64el.deb',
			'libgcc1-dbg_6.3.0-18+deb9u1_s390x.deb'
		]

		for fname in fnames:
			if os.path.exists(fname): continue
			url = 'http://http.us.debian.org/debian/pool/main/g/gcc-6/' + fname
			os.system('wget '+url)

			fname2 = fname.replace('-gdb', '')
			if os.path.exists(fname2): continue
			url = 'http://http.us.debian.org/debian/pool/main/g/gcc-6/' + fname2
			os.system('wget '+url)

		for fname in fnames:
			os.system('ar -vx '+fname)
			os.system('tar -xvf data.tar.xz')

	elif sys.argv[1] == 'harvest':
		for fpath in get_files('.so.1'):
			(output, _) = shellout(['file', fpath])
			info = (output.split(': ')[1]).split(', ')
			assert 'ELF' in info[0] and ('MSB' in info[0] or 'LSB' in info[0])
			assert info[4].startswith('BuildID')
			endian = 'big' if 'MSB' in info[0] else 'little'
			build_id = info[4].split('=')[1]

			debug_path = './usr/lib/debug/.build-id/%s/%s.debug' % (build_id[0:2], build_id[2:])
			assert os.path.exists(debug_path)
			print('%s build_id=%s' % (fpath, build_id))
			print('\tendian=%s' % endian)
			print('\tarch=%s, %s' % (info[1], info[2]))
			print('\tdebug: %s' % debug_path)

