	.section	__TEXT,__text,regular,pure_instructions
	.macosx_version_min 10, 10
	.machine ppc
	.section	__TEXT,__textcoal_nt,coalesced,pure_instructions
	.section	__TEXT,__picsymbolstub1,symbol_stubs,pure_instructions,32
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_main
	.align	4
_main:                                  ; @main
; BB#0:
	li r2, 0
	stw r2, -8(r1)
	stw r3, -12(r1)
	stw r4, -16(r1)
	lwz r2, -12(r1)
                                        ; kill: R4<def> R4<kill>
                                        ; kill: R3<def> R3<kill>
	addi r3, r2, 42
	blr

.subsections_via_symbols

