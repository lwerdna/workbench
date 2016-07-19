	.text
	.file	"hello.c"
	.globl	main
	.align	16, 0x90
	.type	main,@function
main:                                   # @main
# BB#0:
	pushl	%ebp
	movl	%esp, %ebp
	subl	$12, %esp
	movl	12(%ebp), %eax
	movl	8(%ebp), %ecx
	movl	$0, -4(%ebp)
	movl	%ecx, -8(%ebp)
	movl	%eax, -12(%ebp)
	movl	-8(%ebp), %eax
	addl	$42, %eax
	addl	$12, %esp
	popl	%ebp
	retl
.Lfunc_end0:
	.size	main, .Lfunc_end0-main


	.ident	"clang version 3.7.1 (tags/RELEASE_371/final)"
	.section	".note.GNU-stack","",@progbits
