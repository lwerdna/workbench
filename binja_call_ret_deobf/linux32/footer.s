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
