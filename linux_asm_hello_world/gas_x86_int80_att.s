.text

.global	_start

_start:
	movl	$len, %edx	# arg2: message length
	movl	$msg, %ecx	# arg1: message
	movl	$1, %ebx	# arg0: stdout
	movl	$4, %eax	# syscall number (__NR_write)
	int		$0x80

	movl	$0, %ebx	# arg0: status
	movl	$1, %eax	# syscall number (__NR_exit)
	int		$0x80

.data

msg:
	.ascii	"Hello,	World!\n"
	len	=	.	-	msg
