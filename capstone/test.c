/* */
#include <stdint.h>

/* capstone stuff */
#include <capstone/capstone.h>
#include <capstone/arm.h>

int main(int ac, char **av)
{
    int rc = -1;
    uint8_t code[4];

    csh handle; /* capstone handle is typedef'd size_t */
    cs_insn *insn; /* detailed instruction information 
                    cs_disasm() will allocate array of cs_insn here */
    size_t count; /* number of instructions disassembled
                    (number of cs_insn allocated) */

    /* initialize capstone handle */
    if(cs_open(CS_ARCH_ARM, CS_MODE_THUMB, &handle) != CS_ERR_OK) {
        printf("ERROR: cs_open()\n");
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

        count = cs_disasm(handle, code, 
            /* code_size */ 2, 
            /* address */ 0, 
            /* instr count */ 1, 
            /* result */ &insn
        );

        if(count <= 0) {
            printf("%02X %02X    undefined?\n", code[0], code[1]);
        }
        else {
            printf("%02X %02X    %s %s\n", code[0], code[1], insn->mnemonic, insn->op_str);
            cs_free(insn, count);
        }
    }
        
    rc = 0;
    cleanup:
    return rc;
}

