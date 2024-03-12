#!/usr/bin/env python

# 0  04 10 5f e2  subs	r1, pc, #4
# 4  08 2b b1 ec  vldmia	r1!, {d2, d3, d4, d5}
# 8  54 41 02 f3  veor	q2, q1, q2
# c  04 4b 2d ed  vpush	{d4, d5}
#10  70 00 20 e1  bkpt	#0
#14  4e 47 d0 8b  blhi	#0xff411d54
#18  69 17 67 90  rsbls	r1, r7, sb, ror #14
#1c  70 24 5f b5  ldrblt	r2, [pc, #-0x470]
#20  3f 52 52 e1  cmp	r2, pc, lsr r2

a = 0x082bb1ec544102f3044b2ded700020e1
b = 0x4e47d08b6917679070245fb53f5252e1

c = a ^ b

print(c.to_bytes(16))

