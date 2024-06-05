#!/usr/bin/env python

import os

for i in range(1,146+1):
	cmd = 'wget https://developer.arm.com/architectures/instruction-sets/simd-isas/neon/intrinsics?page=%d -O ./html/%d.html' % (i, i)
	print(f'running cmd: {cmd}')
	os.system(cmd)
