BITS 32

default rel
global _main
section .text

_main:
	jmp print_A

print_D:
	mov al, 'D'
	call output
	push print_E
	ret

print_L:
	mov al, 'L'
	call output
	push print_M
	ret

print_K:
	mov al, 'K'
	call output
	push print_L
	ret

print_I:
	mov al, 'I'
	call output
	push print_J
	ret

print_T:
	mov al, 'T'
	call output
	push print_U
	ret

print_P:
	mov al, 'P'
	call output
	push print_Q
	ret

print_U:
	mov al, 'U'
	call output
	push print_V
	ret

print_S:
	mov al, 'S'
	call output
	push print_T
	ret

print_J:
	mov al, 'J'
	call output
	push print_K
	ret

print_W:
	mov al, 'W'
	call output
	push print_X
	ret

print_N:
	mov al, 'N'
	call output
	push print_O
	ret

print_H:
	mov al, 'H'
	call output
	push print_I
	ret

print_A:
	mov al, 'A'
	call output
	push print_B
	ret

print_G:
	mov al, 'G'
	call output
	push print_H
	ret

print_B:
	mov al, 'B'
	call output
	push print_C
	ret

print_Y:
	mov al, 'Y'
	call output
	push print_Z
	ret

print_Z:
	mov al, 'Z'
	call output
	push exit
	ret

print_M:
	mov al, 'M'
	call output
	push print_N
	ret

print_V:
	mov al, 'V'
	call output
	push print_W
	ret

print_Q:
	mov al, 'Q'
	call output
	push print_R
	ret

print_F:
	mov al, 'F'
	call output
	push print_G
	ret

print_X:
	mov al, 'X'
	call output
	push print_Y
	ret

print_C:
	mov al, 'C'
	call output
	push print_D
	ret

print_R:
	mov al, 'R'
	call output
	push print_S
	ret

print_E:
	mov al, 'E'
	call output
	push print_F
	ret

print_O:
	mov al, 'O'
	call output
	push print_P
	ret


exit:
	mov eax, 0x2000001 ; exit
	mov edi, 0
	syscall

output:
	push edi

	mov edx, 1 ; size
	mov edi, buffer
	stosb
	mov esi, buffer ; ptr to string
	mov edi, 1 ; output stream: stdout
	mov eax, 0x2000004 ; write
	syscall

	pop edi
	retn

section .data

buffer:
	db 0, 0, 0, 0, 0, 0, 0, 0, 0
