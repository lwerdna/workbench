#include <stdio.h>
#include <stdlib.h>

//#define __STDC_LIMIT_MACROS
//#define __STDC_CONSTANT_MACROS

#include <llvm/MC/MCDisassembler.h>
#include <llvm-c/Target.h>

int main()
{
    int rc = -1;
    uint8_t code[4];

    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllDisassemblers();

    LLVMDisasmContextRef dc = LLVMCreateDisasm ("thumb-unknown-linux-gnu", 
        NULL, 0, NULL, NULL);

    if (dc == NULL) {
        printf("ERROR: LLVMCreateDisasm()");
        goto cleanup;
    }

    for(int i=0; i<65536; ++i) {
        *(uint16_t *)code = (uint16_t)i;

        /* skip 32-bit extended */
        {
            uint16_t instr_word = *(uint16_t *)code;
        	uint16_t tmp = (instr_word & 0xF800)>>11;
	        if(((tmp & 0x1F)==0x1D)) continue;
        	if(((tmp & 0x1F)==0x1E)) continue;
        	if(((tmp & 0x1F)==0x1F)) continue;
        }

        char buf[256] = {0};

        size_t insn_len = LLVMDisasmInstruction(
            dc, /* disasm context */
            code, /* source data */ 
            2, /* length of source data */ 
            0, /* address */ 
            buf, /* output buf */
            256
        );

        if(insn_len <= 0) {
            printf("%02X %02X    undefined?\n", code[0], code[1]);
        }
        else {
            printf("%02X %02X    %s\n", code[0], code[1], buf);
        }
    }

    rc = 0;
    cleanup:
    return rc;
}
