extern magic_square

global	_start

section .text

_start:
	mov		rax, 0		; __NR_read
	mov		rdi, 0		; stdin
	mov		rsi, buffer	; destination buffer
	mov		edx, 9		; buffer size
	syscall

; call magic square
	mov		rdi, buffer	; arg0
	call	magic_square

; DONE, exit
	mov		rdi, 0		; arg0: status
	mov		rax, 60		; __NR_exit
	syscall

section .data

section .bss

buffer:	resb 9
