.syntax unified

.text

movw	r1, #0x9000
movt	r1, #0x4000

// syntax is:
// MRC2{cond} coproc, #opcode1, Rt, CRn, CRm{, #opcode2}

// MIDR, Main ID Register
mrc		p15, #0, r0, c0, c0, #0
str		r0, [r1]

// ID_PFR0, Processor Feature Register 0
mrc		p15, #0, r0, c0, c1, #0
str		r0, [r1, #4]

mrc		p15, #0, r0, c0, c1, #1
str		r0, [r1, #8]

mrc		p15, #0, r0, c0, c1, #2
str		r0, [r1, #12]

mrc		p15, #0, r0, c0, c1, #3
str		r0, [r1, #16]

// ID_ISAR0, Processor Feature Register 0
mrc		p15, #0, r0, c0, c2, #0
str		r0, [r1, #20]

mrc		p15, #0, r0, c0, c2, #1
str		r0, [r1, #24]

mrc		p15, #0, r0, c0, c2, #2
str		r0, [r1, #28]

mrc		p15, #0, r0, c0, c2, #3
str		r0, [r1, #32]

mrc		p15, #0, r0, c0, c2, #4
str		r0, [r1, #36]

mrc		p15, #0, r0, c0, c2, #5
str		r0, [r1, #40]

// clear the up 64-byte boundary
mov		r0, #0
str		r0, [r1, #44]
str		r0, [r1, #48]
str		r0, [r1, #52]
str		r0, [r1, #56]
str		r0, [r1, #60]

done:
b	done

.end


