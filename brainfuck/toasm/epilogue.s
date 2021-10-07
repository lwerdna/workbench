
exit:
	mov		rax, 0x2000001 ; exit
	mov		rdi, 0
	syscall

input:
	push	rdi

	mov		rdx, 1 ; size
	mov		rsi, rdi ; ptr to string
	mov		rdi, 0 ; input stream: stdin
	mov		rax, 0x2000003 ; read
	syscall

	pop		rdi
	retn

output:
	push	rdi

	mov		rdx, 1	; size
	mov		rsi, rdi ; ptr to string
	mov		rdi, 1 ; output stream: stdout
	mov		rax, 0x2000004 ; write
	syscall

	pop		rdi
	retn

