BITS 64

default rel

global _dream_cfg

section .text

# attempt to get the "running example" from the DREAM decompiler PDF
# "No More Gotos: Decompilation Using Pattern-Independent Control-Flow Structuring and Semantics-Preserving Transformations"
_dream_cfg:
	push	rbp
	mov		rbp, rsp
	sub		rsp, 0x20

	.A:
	nop
	cmp		byte [rbp-1], 1
	je		.c1

	.b1:
	nop
	cmp		byte [rbp-2], 1
	je		.b2

	.n4:
	nop
	jmp		.n5

	.c1:
	cmp		byte [rbp-3], 1
	je		.n1

	.c2:
	cmp		byte [rbp-4], 1
	je		.n2

	.n3:
	nop
	jmp		.c3

	.n1:
	nop
	jmp		.c1

	.n2:
	nop
	jmp		.n9

	.c3:
	cmp		byte [rbp-5], 1
	je		.c1
	jmp		.n9

	.b2:
	cmp		byte [rbp-6], 1
	je		.n6

	.n5:
	nop
	jmp		.n7

	.n6:
	nop
	jmp		.n7

	.n7:
	nop
	jmp		.d1

	.d1:
	cmp		byte [rbp-7], 1
	je		.d3

	.d2:
	cmp		byte [rbp-8], 1
	je		.n8
	jmp		.n9

	.d3:
	cmp		byte [rbp-9], 1
	je		.n8
	jmp		.n9

	.n8:
	nop
	jmp		.d1

	.n9:
	add		rsp, 0x10
	pop		rbp
	retn
