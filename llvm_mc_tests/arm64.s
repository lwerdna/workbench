.text
.globl _mylabel
.globl mylabel
.globl _start
.globl _main
.org 0x8000
_main:
start:
ldaxrb w1, [sp]
ldaxrb w2, [sp]
ldaxrb w3, [sp]
ldaxrb w5, [sp]
ldaxrb w6, [sp]
mylabel:
ldaxrb w7, [sp]
ldaxrb w8, [sp]
ldaxrb w9, [sp]
ldaxrb w10, [sp]
b mylabel
ldaxrb w11, [sp]
ldaxrb w12, [sp]
.ltorg
.long 0xDEADBEEF
