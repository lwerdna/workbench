	.text
	.file	"hello.c"
	.globl	main
	.align	2
	.type	main,@function
main:                                   // @main
// BB#0:
	sub	sp, sp, #16             // =16
	str	wzr, [sp, #12]
	str	w0, [sp, #8]
	str	 x1, [sp]
	ldr	w0, [sp, #8]
	add	w0, w0, #42             // =42
	add	sp, sp, #16             // =16
	ret
.Lfunc_end0:
	.size	main, .Lfunc_end0-main


	.ident	"clang version 3.7.1 (tags/RELEASE_371/final)"
	.section	".note.GNU-stack","",@progbits
