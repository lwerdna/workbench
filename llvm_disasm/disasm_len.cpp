/* I'm trying to just ask LLVM for the length, somehow skipping the work
	required to produce a string for each instruction */

#include <stdio.h>
#include <stdlib.h>

/* /usr/local/include/llvm
   /usr/local/include/llvm-c */
#include <llvm-c/Target.h>
#include <llvm-c/Disassembler.h>
#include <llvm/MC/MCDisassembler/MCDisassembler.h>

int main()
{
    int rc = -1;
    uint8_t code[] = {
        0x5B, 0x6A, 0x01, 0x68, 0x0C, 0x00, 0x40, 0x00, 0x50, 0x68, 0xAC, 0x6B, 0x21, 0x00, 0x51, 0x41,
        0x57, 0xBF, 0x00, 0x00, 0x80, 0x00, 0x6A, 0x07, 0x5A, 0xBE, 0xAC, 0x6B, 0x21, 0x00, 0x6A, 0x32,
        0x41, 0x5A, 0x45, 0x29, 0xC0, 0x6A, 0x09, 0x58, 0x0F, 0x05, 0x39, 0xC7, 0x0F, 0x85, 0xF5, 0xFE,
        0xFF, 0xFF, 0xBE, 0x00, 0x00, 0x40, 0x00, 0x89, 0xFA, 0x29, 0xF2, 0x74, 0x15, 0x01, 0xD5, 0x01,
        0x54, 0x24, 0x08, 0x01, 0x54, 0x24, 0x18, 0x89, 0xD9, 0x29, 0xF1, 0xC1, 0xE9, 0x03, 0xFC, 0xF3,
        0x48, 0xA5, 0x97, 0x48, 0x89, 0xDE, 0x50, 0x92, 0xAD, 0x50, 0x48, 0x89, 0xE1, 0xAD, 0x97, 0xAD,
        0x44, 0x0F, 0xB6, 0xC0, 0x48, 0x87, 0xFE, 0xFF, 0xD5, 0x59, 0xC3
    };

    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllDisassemblers();

	/* get context (the reference is an opaque void *) but behind it is some
		specific context */
    LLVMDisasmContextRef contextR = LLVMCreateDisasm ("x86_64-unknown-linux-gnu", 
        NULL, 0, NULL, NULL);

    if (contextR == NULL) {
        printf("ERROR: LLVMCreateDisasm()");
        goto cleanup;
    }

	LLVMDisasmContext *context = (LLVMDisasmContext *)contextR;

	/* the context will return something that subclasses MCDisassembler, like
		X86GenericDisassembler */
	const MCDisassembler *disAsm = context->getDisAsm();

	MCInst instr;
	uint64_t addr = 0;
	uint64_t len;
	ArrayRef<uint8_t> dataAR(code, sizeof(code));
	MCDisassembler::DecodeStatus decodeStat;

    for(unsigned int offs=0; offs<sizeof(code); ) {
		decodeStat = DisAsm->getInstruction(
			instr, /* [out] the resulting instruction */
			len, /* [out] the instruction length */
			dataAR, /* wrap data in some ArrayRef bullshit */
			offs, /* address to consider instructions at */
			nulls(), /* vstream */
			nulls() /* cstream */
		);

		if(decodeStat != MCDisassembler::Success) {
			printf("ERROR!\n");
			goto cleanup;
		}
	
		printf("at %02X instr has %d bytes ", len);	
		for(int j=0; j<len; ++j)
			printf("%02X ", code[j])
		printf("\n");
		
		offs += len;
    }

    rc = 0;
    cleanup:
    return rc;
}
