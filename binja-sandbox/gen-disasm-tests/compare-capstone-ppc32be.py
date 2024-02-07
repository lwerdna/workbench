#!/usr/bin/env python

import re

import tests_ppc32be

from capstone import *

md = Cs(CS_ARCH_PPC, CS_MODE_BIG_ENDIAN)

for addr, encoding_txt, instxt in tests_ppc32be.tests:
    # convert our decimal offsets to hex
    # eg: "stwu r1, -16(r1)" -> "stwu r1, -0x10(r1)"
    if m := re.match(r'^(.*[^x\d])(\d+)(\(.*)', instxt):
        if int(m.group(2)) > 8:
            instxt = m.group(1) + hex(int(m.group(2))) + m.group(3)

    # drop '0x' on small numeric literals
    # eg: "addis r30, r30, 0x4" -> "addis r30, r30, 4"
    if m := re.match(r'^(.*, )(0x\d+)(.*)', instxt):
        if int(m.group(2), 16) <= 8:
            instxt = m.group(1) + str(int(m.group(2), 16)) + m.group(3)

    encoding = bytes.fromhex(encoding_txt)
    csinstr = next(md.disasm(encoding, addr))
    csinstxt = csinstr.mnemonic + ' ' + csinstr.op_str

    print(f'{addr:X} {encoding_txt} "{instxt}" vs "{csinstxt}"')
    assert instxt == csinstxt
