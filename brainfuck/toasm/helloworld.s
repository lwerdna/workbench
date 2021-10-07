; brainfuck assembly translation of ../helloworld.bf

default rel
global _main
section .text

_main:
	mov rdi, rsp
	sub rdi, 0x4000
	mov rcx, 0x4000
	mov al, 0
	rep stosb
	sub rdi, 0x4000

body:

	cmp byte [rdi], 0
	jz loc_23
loc_0:
	call input
	call output
	cmp byte [rdi], 0
	jz loc_5
loc_3:
	call output
	cmp byte [rdi], 0
	jnz loc_3
loc_5:
	call input
	call output
	call output
	call input
	call input
	call input
	inc byte [rdi]
	call input
	dec byte [rdi]
	call input
	dec rdi
	inc rdi
	call input
	cmp byte [rdi], 0
	jz loc_20
loc_19:
	cmp byte [rdi], 0
	jnz loc_19
loc_20:
	call output
	call output
	cmp byte [rdi], 0
	jnz loc_0
loc_23:
	add byte [rdi], 8
	cmp byte [rdi], 0
	jz loc_53
loc_25:
	inc rdi
	add byte [rdi], 4
	cmp byte [rdi], 0
	jz loc_39
loc_28:
	inc rdi
	add byte [rdi], 2
	inc rdi
	add byte [rdi], 3
	inc rdi
	add byte [rdi], 3
	inc rdi
	inc byte [rdi]
	sub rdi, 4
	dec byte [rdi]
	cmp byte [rdi], 0
	jnz loc_28
loc_39:
	inc rdi
	inc byte [rdi]
	inc rdi
	inc byte [rdi]
	inc rdi
	dec byte [rdi]
	add rdi, 2
	inc byte [rdi]
	cmp byte [rdi], 0
	jz loc_50
loc_48:
	dec rdi
	cmp byte [rdi], 0
	jnz loc_48
loc_50:
	dec rdi
	dec byte [rdi]
	cmp byte [rdi], 0
	jnz loc_25
loc_53:
	add rdi, 2
	call output
	inc rdi
	sub byte [rdi], 3
	call output
	add byte [rdi], 7
	call output
	call output
	add byte [rdi], 3
	call output
	add rdi, 2
	call output
	dec rdi
	dec byte [rdi]
	call output
	dec rdi
	call output
	add byte [rdi], 3
	call output
	sub byte [rdi], 6
	call output
	sub byte [rdi], 8
	call output
	add rdi, 2
	inc byte [rdi]
	call output
	inc rdi
	add byte [rdi], 2
	call output

exit:
	mov rax, 0x2000001 ; exit
	mov rdi, 0
	syscall

input:
	push rdi

	mov rdx, 1 ; size
	mov rsi, rdi ; ptr to string
	mov rdi, 0 ; input stream: stdin
	mov rax, 0x2000003 ; read
	syscall

	pop rdi
	retn

output:
	push rdi

	mov rdx, 1 ; size
	mov rsi, rdi ; ptr to string
	mov rdi, 1 ; output stream: stdout
	mov rax, 0x2000004 ; write
	syscall

	pop rdi
	retn


