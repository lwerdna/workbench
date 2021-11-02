BITS 64

default rel
global _main
section .text

_main:
	jmp print_A

print_N:
	mov al, 'N'
	call output
	mov rax, print_O
	push rax
	ret

print_O:
	mov al, 'O'
	call output
	mov rax, print_P
	push rax
	ret

print_J:
	mov al, 'J'
	call output
	mov rax, print_K
	push rax
	ret

print_H:
	mov al, 'H'
	call output
	mov rax, print_I
	push rax
	ret

print_E:
	mov al, 'E'
	call output
	mov rax, print_F
	push rax
	ret

print_W:
	mov al, 'W'
	call output
	mov rax, print_X
	push rax
	ret

print_F:
	mov al, 'F'
	call output
	mov rax, print_G
	push rax
	ret

print_G:
	mov al, 'G'
	call output
	mov rax, print_H
	push rax
	ret

print_S:
	mov al, 'S'
	call output
	mov rax, print_T
	push rax
	ret

print_V:
	mov al, 'V'
	call output
	mov rax, print_W
	push rax
	ret

print_I:
	mov al, 'I'
	call output
	mov rax, print_J
	push rax
	ret

print_K:
	mov al, 'K'
	call output
	mov rax, print_L
	push rax
	ret

print_R:
	mov al, 'R'
	call output
	mov rax, print_S
	push rax
	ret

print_B:
	mov al, 'B'
	call output
	mov rax, print_C
	push rax
	ret

print_A:
	mov al, 'A'
	call output
	mov rax, print_B
	push rax
	ret

print_P:
	mov al, 'P'
	call output
	mov rax, print_Q
	push rax
	ret

print_T:
	mov al, 'T'
	call output
	mov rax, print_U
	push rax
	ret

print_C:
	mov al, 'C'
	call output
	mov rax, print_D
	push rax
	ret

print_X:
	mov al, 'X'
	call output
	mov rax, print_Y
	push rax
	ret

print_U:
	mov al, 'U'
	call output
	mov rax, print_V
	push rax
	ret

print_M:
	mov al, 'M'
	call output
	mov rax, print_N
	push rax
	ret

print_Q:
	mov al, 'Q'
	call output
	mov rax, print_R
	push rax
	ret

print_Z:
	mov al, 'Z'
	call output
	mov rax, exit
	push rax
	ret

print_D:
	mov al, 'D'
	call output
	mov rax, print_E
	push rax
	ret

print_L:
	mov al, 'L'
	call output
	mov rax, print_M
	push rax
	ret

print_Y:
	mov al, 'Y'
	call output
	mov rax, print_Z
	push rax
	ret

exit:
	mov rax, 0x2000001 ; exit
	mov rdi, 0
	syscall

output:
	push rdi

	mov edx, 1 ; size
	mov rdi, buffer
	stosb
	mov rsi, buffer ; ptr to string
	mov rdi, 1 ; output stream: stdout
	mov rax, 0x2000004 ; write
	syscall

	pop rdi
	retn

section .data

buffer:
	db 0, 0, 0, 0, 0, 0, 0, 0, 0
