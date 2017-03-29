#!/usr/bin/python

import re
import os
import sys
from time import localtime, mktime, struct_time

sys.path.append(os.environ['PATH_AUTILS_PY'])
import utils

action = '-1'
if len(sys.argv)>1:
    action = sys.argv[1]

cmds = [ \
    "adb shell \"ls -l /sdcard/DCIM/Camera/*.jpg\"", \
    "adb shell \"ls -l /sdcard/DCIM/Camera/*.mp4\"", \
]

# localtime() returns time.struct_time, mktime() returns float
epoch_now = mktime(localtime())
print "epoch NOW: %d" % epoch_now

for cmd in cmds:
    output = utils.runGetOutput(cmd, True)
  
    if re.search(r': No such file or directory', output):
        continue

    if re.search(r'not found: ', output):
        continue

    lines = output.split("\n")
    for i,l in enumerate(lines):
        if not l:
            continue
   
        # calculate time of the file!
        #
        print "splitting line: -%s-" % l
		# -rw-rw---- 1 root sdcard_rw  2674934 2015-08-27 07:03 /sdcard/DCIM/Camera/IMG_20150827_070354.jpg
        m = re.match('^(.*?)\s+(.*?)\s+(.*?)\s+(.*?)\s+(.*?)\s+(.*?)\s+(.*?)\s+(.*?)$', l)
        if not m:
            continue

        (perms, dunno, owner, dunno, size, date, ftime, fpath) = m.group(1,2,3,4,5,6,7,8)
        # parsing string like "2013-07-31"
        (year, month, day) = map(lambda x: int(x), date.split('-'))
        # parsing string like "15:44"
        (hour, minute) = map(lambda x: int(x), ftime.split(':'))
        #
        epoch_file = mktime(struct_time([year, month, day, hour, minute, 0, 0, 1, -1]))

        fpath = fpath.rstrip()
        print "considering file \"%s\" with time %04d/%02d/%02d %02d:%02d (epoch: %d)" % \
            (fpath, year, month, day, hour, minute, epoch_file)
    
        if action == 'all':
            # k then just do it
            pass

        elif re.match(r'-[0-9]+', action):
            num_days = -1 * int(action)

            if epoch_now - epoch_file < (num_days * 24 * 60 * 60):
                # good! within range!
                pass
            else:
                print "    TOO OLD!"
                continue

        else:
            print "unknown action: %s" % action
            sys.exit(-1);
   
        if os.path.exists(fpath):
            print "    EXISTS ALREADY!"
            continue

        #print "executing:\n    %s" % cmd
        cmd = 'adb pull "%s"' % fpath
        output = utils.runGetOutput(cmd, True)
        print output

        if re.match(r'^.*?\.jpg$', fpath):
            #cmd = 'mogrify -strip -resize 512x384 %s' % fpath
            #cmd = 'mogrify -strip -resize 1024x768 %s' % fpath
            cmd = 'mogrify -strip -resize 2048x1536 %s' % fpath
            #cmd = 'mogrify -strip %s' % fpath
            output = utils.runGetOutput(cmd, True)
            print output

