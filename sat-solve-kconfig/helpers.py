#!/usr/bin/env python

import os

def get_kernel_path():
    PATH_DOWNLOADS = os.path.join(os.environ['HOME'], 'Downloads')
    candidates = []
    candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-3.10'))
    candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-3.10.1'))
    candidates.append(os.path.join(PATH_DOWNLOADS, 'linux-master'))
    for candidate in candidates:
        if os.path.exists(candidate):
            return candidate

def get_kconf_object(ARCH='arm'):
	# kconfiglib is configured through the environment
	os.environ['srctree'] = get_kernel_path()
	os.environ['SRCARCH'] = ARCH
	kconf = kconfiglib.standard_kconfig()
    return kconf

if __name__ == '__main__':
    print(f'kernel path: {get_kernel_path()}')
