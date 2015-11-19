#!/usr/bin/env python

import os
import sys
from struct import pack, unpack

fobj = open(sys.argv[1], 'rb')

# reading struct boot_img_hdr here
magic = fobj.read(8)
print "magic: %s" % magic

(kernel_size, kernel_addr, ramdisk_size, ramdisk_addr, \
    second_size, second_addr, tags_addr, page_size, \
    unused0, unused1) = unpack('<10I', fobj.read(10*4))

print "kernel_size: 0x%X (%d)" % (kernel_size, kernel_size)
print "kernel_addr: 0x%X (%d)" % (kernel_addr, kernel_addr)
print "ramdisk_size: 0x%X (%d)" % (ramdisk_size, ramdisk_size)
print "ramdisk_addr: 0x%X (%d)" % (ramdisk_addr, ramdisk_addr)
print "second_size: 0x%X (%d)" % (second_size, second_size)
print "second_addr: 0x%X (%d)" % (second_addr, second_addr)
print "tags_addr: 0x%X (%d)" % (tags_addr, tags_addr)
print "page_size: 0x%X (%d)" % (page_size, page_size)

name = fobj.read(16)
print "name: %s" % name

cmdline = fobj.read(512)
print "cmdline: %s" % cmdline

id = fobj.read(8*4)
print "id: " + repr(id)

# number of pages needed rounds upward
pages_kernel = int((kernel_size + page_size - 1) / page_size)
pages_ramdisk = int((ramdisk_size + page_size - 1) / page_size)
pages_second = int((second_size + page_size - 1) / page_size)

fobj.seek(page_size)

print "reading kernel.zImage from offset 0x%X (%d)" % (fobj.tell(), fobj.tell())
tmp = open('kernel.zImage', 'wb')
tmp2 = fobj.read(pages_kernel * page_size)
tmp.write(tmp2)
print "wrote 0x%X (%d) bytes" % (len(tmp2), len(tmp2))
tmp.close()

print "reading ramdisk.gz from offset 0x%X (%d)" % (fobj.tell(), fobj.tell())
tmp = open('ramdisk.gz', 'wb')
tmp2 = fobj.read(pages_ramdisk * page_size)
tmp.write(tmp2)
print "wrote 0x%X (%d) bytes" % (len(tmp2), len(tmp2)) 
tmp.close()

if pages_second:
    print "reading second.bin from offset 0x%X (%d)" % (fobj.tell(), fobj.tell())
    tmp = open('second.bin', 'wb')
    tmp2 = fobj.read(pages_second * page_size)
    tmp.write(tmp2)
    print "wrote 0x%X (%d) bytes" % (len(tmp2), len(tmp2)) 
    tmp.close()

# done
fobj.close()

# post processing
# zImage starts with arch/arm/boot/compressed/head.S
fobj = open('kernel.zImage', 'rb')
if 8*"\x00\x00\xA0\xE1" != fobj.read(32):
    raise Exception("expected 8 \"mov r0, r0\" at start of zImage")
# skip the branch
fobj.read(4)
# read magic number
if "\x18\x28\x6f\x01" != fobj.read(4):
    raise Exception("expected magic number 0x016f2818 in zImage")
# read load/run zImage address
start = unpack('<I', fobj.read(4))[0]
edata = unpack('<I', fobj.read(4))[0]
print "zImage start: 0x%X (%d)" % (start, start)
print "zImage edata: 0x%X (%d)" % (edata, edata)

fobj.seek(0)
tmp = fobj.read()
idx = tmp.find("\x8b\x1f")
print "found kernel.gz 0x%X (%d) bytes into kernel.zImage" % (idx, idx)
tmp = tmp[idx+2:]
idx = tmp.find("\x8b\x1f")
print "found kernel.gz 0x%X (%d) bytes into kernel.zImage" % (idx, idx)
tmp = tmp[idx+2:]
idx = tmp.find("\x8b\x1f")
print "found kernel.gz 0x%X (%d) bytes into kernel.zImage" % (idx, idx)
tmp = tmp[idx+2:]
idx = tmp.find("\x8b\x1f")
print "found kernel.gz 0x%X (%d) bytes into kernel.zImage" % (idx, idx)
tmp = tmp[idx:]
fobj = open('kernel.gz', 'wb')
fobj.write(tmp)
print "wrote 0x%X (%d) bytes to kernel.gz" % (len(tmp), len(tmp))
