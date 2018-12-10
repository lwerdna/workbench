.text

.global	_start

_start:
	movq	$len, %rdx	# arg2: message length
	movq	$msg, %rsi	# arg1: message
	movq	$1, %rdi	# arg0: stdout
	movq	$1, %rax	# 64-bit syscall number (__NR_write)
	syscall

	movq	$0, %rdi	# arg0: status
	movq	$60, %rax	# 64-bit syscall number (__NR_exit)
	syscall

.data

msg:
	.ascii	"Hello,	World!\n"
	len	=	.	-	msg
