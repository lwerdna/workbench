BITS 64

default rel

global _dream_cfg

section .text

_dream_cfg:
	push	rbp
	mov		rbp, rsp
	sub		rsp, 0x20

	.A:
	cmp byte [rbp-1], 0
	jne		.c1
	jmp		.b1

	;	
	; R1
	;
	.c1:
	cmp byte [rbp-2], 0
	jne		.n1
	jmp		.c2

	.n1:
	nop
	jmp		.c1;

	.c2:
	cmp byte [rbp-3], 0
	jne		.n2
	jmp		.n3

	.n2:
	nop
	jmp		.n9;

	.n3:
	nop
	jmp		.c3;

	.c3:
	nop
	jmp		.c1;

	;
	; R2
	;
	.b1:
	cmp byte [rbp-4], 0
	jne		.b2
	jmp		.n4
	
	.b2:
	cmp byte [rbp-5], 0
	jne		.n6
	jmp		.n5

	.n4:
	nop
	jmp		.n5;

	.n5:
	nop
	jmp		.n7;

	.n6:
	nop
	jmp		.n7;

	.n7:
	nop
	jmp		.d1;

	;
	; R3
	;
	.d1:
	cmp byte [rbp-6], 0
	jne		.d3
	jmp		.d2

	.d2:
	cmp byte [rbp-7], 0
	jne		.n8
	jmp		.n9

	.d3:
	cmp byte [rbp-8], 0
	jne		.n8
	jmp		.n9

	.n8:
	nop
	jmp		.d1;

	.n9:
	add		rsp, 0x10
	pop		rbp
	retn
