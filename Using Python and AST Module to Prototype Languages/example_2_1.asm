default rel
global _main
section .text

extern init
extern unknown
extern rotation
extern translation

_main:
	push rbp
	mov rbp, rsp
	push 1
	push 0
	push 1
	push 0
	call init
	push 0
	push 1
	call translation
.loc_0001:
	call unknown
	cmp rax, 1
	je .loc_0002
	call unknown
	cmp rax, 1
	jne .loc_0003
	push 0
	push 1
	call translation
	push 3
	push 2
	call translation
	jmp .loc_0004
.loc_0003:
	push 90
	push 0
	push 0
	call rotation
.loc_0004:
	jmp .loc_0001
.loc_0002:
	mov rax, 0
	pop rbp
	retn
