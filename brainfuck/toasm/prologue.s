default rel
global _main
section .text

_main:
	mov rdi, rsp
	sub rdi, 0x4000
	mov rcx, 0x4000
	mov	al, 0
	rep stosb
	sub rdi, 0x4000

body:
