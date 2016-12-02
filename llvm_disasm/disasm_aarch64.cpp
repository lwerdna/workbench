#include <stdio.h>
#include <stdlib.h>

#include <llvm-c/Disassembler.h>
#include <llvm-c/Target.h>

int main()
{
    int rc = -1;
    uint8_t code[] = {
		0xFF, 0x43, 0x00, 0xD1, 0xFF, 0x0F, 0x00, 0xB9, 
		0xE0, 0x0B, 0x00, 0xB9, 0xE1, 0x03, 0x00, 0xF9, 
		0xE0, 0x0B, 0x40, 0xB9, 0x00, 0xA8, 0x00, 0x11, 
		0xFF, 0x43, 0x00, 0x91, 0xC0, 0x03, 0x5F, 0xD6
	};

    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllDisassemblers();

    LLVMDisasmContextRef dc = LLVMCreateDisasm ("aarch64-none-none", 
        NULL, 0, NULL, NULL);

    if (dc == NULL) {
        printf("ERROR: LLVMCreateDisasm()");
        goto cleanup;
    }

    for(unsigned int offs=0; offs<sizeof(code); ) {
        char mnemonic[256] = {0};

        size_t insn_len = LLVMDisasmInstruction(
            dc, /* disasm context */
            code + offs, /* source data */ 
            sizeof(code) - offs, /* length of source data */ 
            offs, /* address */ 
            mnemonic, /* output buf */
            sizeof(mnemonic) /* size of output buf */
        );

        if(insn_len <= 0) {
            printf("%04X: undefined?\n", offs);
            break;
        }
        else {
            printf("%04X: %s\n", offs, mnemonic);
        }

        offs += insn_len;
    }

    rc = 0;
    cleanup:
    return rc;
}
