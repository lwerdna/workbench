global	_start

section .text

_start:
	; get argv[0][0]
	; lea		rsi, [rsp+0x10]	; get argv[0]
	; mov		al, [rsi]		; get first character
	
	mov		rax, 0		; __NR_read
	mov		rdi, 0		; stdin
	mov		rsi, buffer	; destination buffer
	mov		edx, 1		; buffer size
	syscall

	mov		al, [buffer]
	cmp		al, 0x40
	jg		is_greater

is_less:
	mov		rdx, msglen1
	mov		rsi, msg1
	mov		rdi, 1
	mov		rax, 1
	syscall
	jmp done

is_greater:
	mov		rdx, msglen0
	mov		rsi, msg0
	mov		rdi, 1
	mov		rax, 1
	syscall
	jmp done

done:
	mov		rdi, 0		; arg0: status
	mov		rax, 60		; __NR_exit
	syscall

section .data

msg0:		db	"greater", 0x0a, 0
msglen0:	equ	$ - msg0

msg1:		db	"less", 0x0a, 0
msglen1:	equ	$ - msg1

section .bss

buffer:	resb 1
