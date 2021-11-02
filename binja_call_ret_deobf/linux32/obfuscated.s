BITS 32

global _start
section .text

_start:
	jmp print_A

print_Q:
	mov al, 'Q'
	call output
	push print_R
	ret

print_O:
	mov al, 'O'
	call output
	push print_P
	ret

print_J:
	mov al, 'J'
	call output
	push print_K
	ret

print_P:
	mov al, 'P'
	call output
	push print_Q
	ret

print_Z:
	mov al, 'Z'
	call output
	push exit
	ret

print_V:
	mov al, 'V'
	call output
	push print_W
	ret

print_A:
	mov al, 'A'
	call output
	push print_B
	ret

print_H:
	mov al, 'H'
	call output
	push print_I
	ret

print_C:
	mov al, 'C'
	call output
	push print_D
	ret

print_G:
	mov al, 'G'
	call output
	push print_H
	ret

print_T:
	mov al, 'T'
	call output
	push print_U
	ret

print_W:
	mov al, 'W'
	call output
	push print_X
	ret

print_Y:
	mov al, 'Y'
	call output
	push print_Z
	ret

print_D:
	mov al, 'D'
	call output
	push print_E
	ret

print_M:
	mov al, 'M'
	call output
	push print_N
	ret

print_X:
	mov al, 'X'
	call output
	push print_Y
	ret

print_F:
	mov al, 'F'
	call output
	push print_G
	ret

print_K:
	mov al, 'K'
	call output
	push print_L
	ret

print_B:
	mov al, 'B'
	call output
	push print_C
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

print_N:
	mov al, 'N'
	call output
	push print_O
	ret

print_L:
	mov al, 'L'
	call output
	push print_M
	ret

print_U:
	mov al, 'U'
	call output
	push print_V
	ret

print_I:
	mov al, 'I'
	call output
	push print_J
	ret

print_S:
	mov al, 'S'
	call output
	push print_T
	ret

exit:
	mov		ebx, 0			; arg0: status
	mov		eax, 1			; __NR_exit
	int		0x80

output:
	mov		edi, buffer
	stosb
	mov		edx, 1			; arg2: message length
	mov		ecx, buffer		; arg1: message
	mov		ebx, 1			; arg0: stdout
	mov		eax, 4			; __NR_write
	int		0x80
	retn

section .data

buffer:
	db 0, 0, 0, 0, 0, 0, 0, 0, 0
