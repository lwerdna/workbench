#!/usr/bin/env python

# download debian shared objects, separate debug symbols, and unstrip them

# apt-get install elfutils to get eu-unstrip tool

import os, sys, re

from subprocess import Popen, PIPE
def shellout(cmd):
    process = Popen(cmd, stdout=PIPE, stderr=PIPE)
    (stdout, stderr) = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    process.wait()
    return (stdout, stderr)

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

def undeb(fpath):
    os.system('ar -vx '+fpath)
    os.system('tar -xvf data.tar.xz')

if __name__ == '__main__':
    if sys.argv[1] == 'fetch':
        urls = [
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_amd64.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_arm64.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_armel.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_armhf.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_i386.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_mips.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_mips64el.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_mipsel.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_ppc64el.deb',
            'http://http.us.debian.org/debian/pool/main/g/gcc-6/libgcc1-dbg_6.3.0-18+deb9u1_s390x.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_amd64.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_arm64.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_armel.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_armhf.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_i386.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_mips64el.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_mipsel.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_ppc64el.deb',
            'http://http.us.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.31-12_s390x.deb',
        ]

        for url in urls:
            fname = url[url.rfind('/')+1:]

            if not os.path.exists(fname):
                os.system('wget '+url)
            undeb(fname)

            url = url.replace('-dbg', '')
            fname = fname.replace('-dbg', '')
            if not os.path.exists(fname):
                os.system('wget '+url)
            undeb(fname)

    elif sys.argv[1] == 'harvest':
        for fpath in dirtree('./lib'):
            if not re.match(r'^.*\.so\.\d$', fpath):
                continue
            #if not 'pthread' in fpath:
            #    continue
            soname = os.path.split(fpath)[-1]
            if os.path.islink(fpath):
                fpath = os.path.realpath(fpath)
            (output, _) = shellout(['file', fpath])
            info = (output.split(': ')[1]).split(', ')
            assert 'ELF' in info[0] and ('MSB' in info[0] or 'LSB' in info[0]), 'didnt find info in: '+output

            endian = 'big' if 'MSB' in info[0] else 'little'
            build_id = None
            for i in info:
                if i.startswith('BuildID'):
                    build_id = i.split('=')[1]
                    break
            assert build_id

            debug_path = './usr/lib/debug/.build-id/%s/%s.debug' % (build_id[0:2], build_id[2:])
            if not os.path.exists(debug_path):
                # report warning?
                continue

            arch_prefix = fpath.split('/')[-2].split('-')[0]
            (base, ext) = re.match(r'^(.*)\.(so\.\d+)$', soname).group(1,2)
            out_fname = '%s_%s.%s' % (base, arch_prefix, ext)

            print('%s build_id=%s' % (fpath, build_id))
            print('\tsoname=%s' % soname)
            print('\tendian=%s' % endian)
            print('\tarch=%s, %s' % (info[1], info[2]))
            print('\tarch_prefix=%s' % arch_prefix)
            print('\tdebug: %s' % debug_path)

            cmd = 'eu-unstrip %s %s --output=%s' % (fpath, debug_path, out_fname)
            print(cmd)
            os.system(cmd)

