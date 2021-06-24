#!/usr/bin/env python

import os, sys, re

from subprocess import Popen, PIPE

def dirtree(root):
	result = []
	for root, dirs, fnames in os.walk(root):
		for dir in dirs:
			#print os.path.join(root, dir)
			pass
		for fname in fnames:
                    
                    fpath = os.path.join(root, fname)
		    result.append(fpath)
	return result

def shellout(cmd):
	#print(' '.join(cmd))
	process = Popen(cmd, stdout=PIPE, stderr=PIPE)
	(stdout, stderr) = process.communicate()
	stdout = stdout.decode("utf-8")
	stderr = stderr.decode("utf-8")
	#print('stdout: -%s-' % stdout)
        #print('stderr: -%s-' % stderr)
	process.wait()
	return stdout

def get_elfs(root):
    result = []

    for path in dirtree(root):
        output = shellout(['file', path])
        if 'ELF' in output:
            result.append(path)

    return result
        
for path in get_elfs('.'):
    cmd = ['gdb', path, '-ex', 'info types', 'info functions', '-ex', 'q']
    output = shellout(cmd)

    outfile = path
    if outfile.startswith('./'):
        outfile = outfile[2:]
    outfile = outfile.replace('/', '_') + '.txt'

    print('writing ' + outfile)
    with open(outfile, 'w') as fp:
        fp.write(output)
