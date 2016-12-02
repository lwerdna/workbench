/* */
#include <stdint.h>

/* capstone stuff /usr/local/include/capstone */
#include <capstone/capstone.h>
#include <capstone/arm64.h>

int main(int ac, char **av)
{
    int rc = -1;

    uint8_t code[] = {
		0xFF, 0x43, 0x00, 0xD1, 0xFF, 0x0F, 0x00, 0xB9, 
		0xE0, 0x0B, 0x00, 0xB9, 0xE1, 0x03, 0x00, 0xF9, 
		0xE0, 0x0B, 0x40, 0xB9, 0x00, 0xA8, 0x00, 0x11, 
		0xFF, 0x43, 0x00, 0x91, 0xC0, 0x03, 0x5F, 0xD6
	};


    csh handle; /* capstone handle is typedef'd size_t */
    cs_insn *insn; /* detailed instruction information 
                    cs_disasm() will allocate array of cs_insn here */
    size_t nInstr; /* number of instructions disassembled
                    (number of cs_insn allocated) */

    /* initialize capstone handle */
    if(cs_open(CS_ARCH_ARM64, 0, &handle) != CS_ERR_OK) {
        printf("ERROR: cs_open()\n");
        goto cleanup;
    }

	
    for(int i=0; i<sizeof(code); ) {

        nInstr = cs_disasm(handle, 
			/* */ code + i, 
            /* code_size */ sizeof(code)-i, 
            /* address */ i, 
            /* instr count */ 1, 
            /* result */ &insn
        );

        if(nInstr != 1) {
            printf("ERROR: cs_disasm()\n");
			goto cleanup;
        }

		for(int j=0; j<insn->size; ++j) printf("%02X ", code[i+j]);
		printf("  %s %s\n", insn->mnemonic, insn->op_str);

        cs_free(insn, nInstr);

		i += insn->size;
    }
        
    rc = 0;
    cleanup:
    return rc;
}

