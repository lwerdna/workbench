#!/usr/bin/env python

import os
import sys
import gnupg

gpg = gnupg.GPG(binary='/usr/local/bin/gpg', homedir='/Users/andrewl/.gnupg/')

path = 'test.txt.gpg'
if sys.argv[1:]:
    path = sys.argv[1]
print "opening %s to crack" % path
fp = open(path)

for i in ["a", "A", "4"]:
    for j in ["s","S","5","2"]:
        for k in ["s","S","5","2"]:
            for l in ["o", "0", "O"]:
                for m in range(1001):
                    candidate = "p%s%s%sw%srd" % (i,j,k,l)
                    if m!=1000:
                        candidate += str(m)
                    print "trying: -%s-" % candidate
                    fp.seek(0)
                    status = gpg.decrypt_file(fp, passphrase=candidate, output="decrypted")
                    if status.ok:
                        print "found it! %s" % candidate
                        sys.exit(-1);
