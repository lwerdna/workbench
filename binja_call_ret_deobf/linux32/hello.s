global	_start

	section .text
_start:
	mov		edx, msglen		; arg2: message length
	mov		ecx, msg		; arg1: message
	mov		ebx, 1			; arg0: stdout
	mov		eax, 4			; __NR_write
	int		0x80
	
	mov		ebx, 0			; arg0: status
	mov		eax, 1			; __NR_exit
	int		0x80

	section .data
msg:		db	"Hello, world!", 0x0a, 0
msglen:	equ	$ - msg
