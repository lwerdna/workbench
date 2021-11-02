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
