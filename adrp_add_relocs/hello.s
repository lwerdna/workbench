.global _start
.align 2

_start:
	// all three of the following options should assemble to:
	//       0: 01 00 00 90                  	adrp	x1, #0
	//       4: 01 00 00 91                  	add	x1, x0, #0
	// with an ARM64_RELOC_PAGE21 on the adrp
	// with an ARM64_RELOC_PAGEOFF12 on the add

	// option1:
	// adrl pseudo instruction should produce adrp, add
	// error: unrecognized instruction mnemonic on clang as
	// Error: unknown mnemonic on GNU assembler from Android NDK
	//adrl	x1, helloworld

	// option2:
	// works with clang as
	// use this @PAGE and @PAGEOFF shit
	adrp	x1, helloworld@PAGE
	add		x1, x1, helloworld@PAGEOFF

	// option3:
	// works with GNU assembler from Android NDK
	// use this :lo12 shit
	// adrp	x1, msg
	// add		x1, x1, :lo12:helloworld	

	mov		x0, #1
	mov		x2, #13
	mov		x16, #4
	svc		#0x80

	mov		x0, #0
	mov		x16, #1
	svc		#0x80

	// so binja will see end of function
	ret

helloworld:
	.ascii  "Hello World!\n"
