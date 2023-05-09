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
	jz loc_571
loc_0:
	call input
	call output
	cmp byte [rdi], 0
	jz loc_137
loc_113:
	call output
	cmp byte [rdi], 0
	jnz loc_113
loc_137:
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
	jz loc_381
loc_373:
	cmp byte [rdi], 0
	jnz loc_373
loc_381:
	call output
	call output
	cmp byte [rdi], 0
	jnz loc_0
loc_571:
	add byte [rdi], 8
	cmp byte [rdi], 0
	jz loc_1443
loc_613:
	inc rdi
	add byte [rdi], 4
	cmp byte [rdi], 0
	jz loc_985
loc_695:
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
	jnz loc_695
loc_985:
	inc rdi
	inc byte [rdi]
	inc rdi
	inc byte [rdi]
	inc rdi
	dec byte [rdi]
	add rdi, 2
	inc byte [rdi]
	cmp byte [rdi], 0
	jz loc_1236
loc_1234:
	dec rdi
	cmp byte [rdi], 0
	jnz loc_1234
loc_1236:
	dec rdi
	dec byte [rdi]
	cmp byte [rdi], 0
	jnz loc_613
loc_1443:
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


