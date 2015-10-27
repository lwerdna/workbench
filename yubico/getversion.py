#!/usr/bin/env python
""" Get version of connected YubiKey. """

import sys
import yubico

try:
    yubikey = yubico.find_yubikey(debug=True)
    print "Version : %s " % yubikey.serial()
except yubico.yubico_exception.YubicoError as e:
    print "ERROR: %s" % e.reason
    sys.exit(1)
