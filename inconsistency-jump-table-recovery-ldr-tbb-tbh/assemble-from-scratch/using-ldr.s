.syntax unified
#.thumb

.globl SetSemaphore

.text

.thumb_func
SetSemaphore:
	push    {r7}
	sub     sp, #0xc
	add     r7, sp, #0
	mov     r3, r0
	mov     r2, r1
	strb    r3, [r7, #7]
	mov     r3, r2
	strb    r3, [r7, #6]
	ldrb    r3, [r7, #7]
	cmp     r3, #8
	bhi     loc_3B6
loc_258:
	adr     r2, jump_table_260
	ldr     pc, [r2, r3, lsl #2]

.byte 0, 0

jump_table_260:
.word loc_284+1
.word loc_2A6+1
.word loc_2C8+1
.word loc_2EA+1
.word loc_30C+1
.word loc_32E+1
.word loc_350+1
.word loc_372+1
.word loc_394+1
	
loc_284:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_298
loc_28A:
	ldr     r3, [pc, #0x134]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x130]
	orr     r3, r3, #0x8000
	str     r3, [r2]
	b       loc_3B6
loc_298:
	ldr     r3, [pc, #0x128]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x124]
	orr     r3, r3, #0x8000
	str     r3, [r2]
	b       loc_3B6
loc_2A6:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_2BA
loc_2AC:
	ldr     r3, [pc, #0x110]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x10c]
	orr     r3, r3, #0x20000
	str     r3, [r2]
	b       loc_3B6
loc_2BA:
	ldr     r3, [pc, #0x108]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x104]
	orr     r3, r3, #0x20000
	str     r3, [r2]
	b       loc_3B6
loc_2C8:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_2DC
loc_2CE:
	ldr     r3, [pc, #0xf0]
	ldr     r3, [r3]
	ldr     r2, [pc, #0xec]
	orr     r3, r3, #0x40000
	str     r3, [r2]
	b       loc_3B6
loc_2DC:
	ldr     r3, [pc, #0xe4]
	ldr     r3, [r3]
	ldr     r2, [pc, #0xe0]
	orr     r3, r3, #0x40000
	str     r3, [r2]
	b       loc_3B6
loc_2EA:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_2FE
loc_2F0:
	ldr     r3, [pc, #0xcc]
	ldr     r3, [r3]
	ldr     r2, [pc, #0xc8]
	orr     r3, r3, #2
	str     r3, [r2]
	b       loc_3B6
loc_2FE:
	ldr     r3, [pc, #0xc4]
	ldr     r3, [r3]
	ldr     r2, [pc, #0xc0]
	orr     r3, r3, #2
	str     r3, [r2]
	b       loc_3B6
loc_30C:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_320
loc_312:
	ldr     r3, [pc, #0xac]
	ldr     r3, [r3]
	ldr     r2, [pc, #0xa8]
	orr     r3, r3, #1
	str     r3, [r2]
	b       loc_3B6
loc_320:
	ldr     r3, [pc, #0xa0]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x9c]
	orr     r3, r3, #1
	str     r3, [r2]
	b       loc_3B6
loc_32E:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_342
loc_334:
	ldr     r3, [pc, #0x88]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x84]
	orr     r3, r3, #0x40
	str     r3, [r2]
	b       loc_3B6
loc_342:
	ldr     r3, [pc, #0x80]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x7c]
	orr     r3, r3, #0x40
	str     r3, [r2]
	b       loc_3B6
loc_350:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_364
loc_356:
	ldr     r3, [pc, #0x68]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x64]
	orr     r3, r3, #0x80
	str     r3, [r2]
	b       loc_3B6
loc_364:
	ldr     r3, [pc, #0x5c]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x58]
	orr     r3, r3, #0x80
	str     r3, [r2]
	b       loc_3B6
loc_372:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_386
loc_378:
	ldr     r3, [pc, #0x44]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x40]
	orr     r3, r3, #0x100
	str     r3, [r2]
	b       loc_3B6
loc_386:
	ldr     r3, [pc, #0x3c]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x38]
	orr     r3, r3, #0x100
	str     r3, [r2]
	b       loc_3B6
loc_394:
	ldrb    r3, [r7, #6]
	cmp     r3, #0
	bne     loc_3A8
loc_39A:
	ldr     r3, [pc, #0x24]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x20]
	orr     r3, r3, #0x200
	str     r3, [r2]
	b       loc_3B4
loc_3A8:
	ldr     r3, [pc, #0x18]
	ldr     r3, [r3]
	ldr     r2, [pc, #0x14]
	orr     r3, r3, #0x200
	str     r3, [r2]
loc_3B4:
	nop
loc_3B6:
	nop
	add     r7, #0xc
	mov     sp, r7
	pop     {r7}
	bx      lr

