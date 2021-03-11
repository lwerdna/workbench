#!/usr/bin/env python
#
# python version of Z0MBIE's PE_STAT for opcode frequency statistics
# http://z0mbie.dreamhosters.com/opcodes.html

import sys
import binaryninja
from collections import defaultdict

opc2count = defaultdict(lambda:0)

#print('opening %s' % sys.argv[1])
bv = binaryninja.BinaryViewType.get_view_of_file(sys.argv[1])
for func in bv.functions:
	for block in func:
		for (toks,length) in block:
			opc = toks[0].text
			opc2count[opc] += 1
			#print('incremented %s, is now: %d' % (opc, opc2count[opc]))

total = sum([x[1] for x in opc2count.items()])

print('op       frequency        %')
for opc in sorted(opc2count.keys(), key=lambda x:opc2count[x], reverse=True):
	print(opc.ljust(8), str(opc2count[opc]).ljust(16), '%.1f%%'%(100.0*opc2count[opc]/total))