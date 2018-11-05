.intel_syntax noprefix

.text

.global	_start

_start:
	mov		rdx, offset len	# arg2: message length
	mov		rsi, offset msg	# arg1: message
	mov		rdi, 1			# arg0: stdout
	mov		rax, 1			# 64-bit syscall number (__NR_write)
	syscall

	mov		rdi, 0			# arg0: status
	mov		rax, 60			# 64-bit syscall number (__NR_exit)
	syscall

.data

msg:
	.ascii	"Hello,	World!\n"
	len	=	.	-	msg
