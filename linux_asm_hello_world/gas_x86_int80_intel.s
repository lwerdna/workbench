.intel_syntax noprefix

.text

.global	_start

_start:
	mov		edx, offset len	# arg2: message length
	mov		ecx, offset msg	# arg1: message
	mov		ebx, 1			# arg0: stdout
	mov		eax, 4			# syscall number (__NR_write)
	int		0x80

	mov		ebx, 0			# arg0: status
	mov		eax, 1			# syscall number (__NR_exit)
	int		0x80

.data

msg:
	.ascii	"Hello,	World!\n"
	len	=	.	-	msg
