/* */
#include <stdint.h>

#include "autils/bytes.h"
#include "autils/parsing.h"

/* capstone stuff */
#include <capstone/capstone.h>
#include <capstone/arm.h>

int main(int ac, char **av)
{
	int rc = -1;
	int code_size, i;
	uint8_t code[4];

	code_size = ac - 1;
	parse_byte_list(av + 1, code_size, code);

	csh handle; /* capstone handle is typedef'd size_t */
	cs_insn *insn = NULL; /* detailed instruction information 
					cs_disasm() will allocate array of cs_insn here */
	size_t count; /* number of instructions disassembled
					(number of cs_insn allocated) */

	/* initialize capstone handle */
	if(cs_open(
	  CS_ARCH_ARM /* cs_arch */,
	  CS_MODE_THUMB /* cs_mode */,
	  &handle /* csh * */) != CS_ERR_OK) {
		printf("ERROR: cs_open()\n");
		goto cleanup;
	}

	printf("disassembling:");
	for(i=0; i<code_size; ++i)
		printf(" %02X", code[i]);
	printf("\n");

	count = cs_disasm(handle, code, 
		code_size /* code_size */, 
		0 /* address */, 
		1 /* instr count */, 
		&insn /* result */
	);

	if(count <= 0) {
		printf("ERROR: cs_disasm() returned %zu\n", count);
		goto cleanup;
	}

	for(i=0; i<insn->size; ++i) {
		printf("%02X", code[i]);
		if(i < (insn->size - 1)) printf(" ");
	}
	printf("\t%s\t%s\n", insn->mnemonic, insn->op_str);
	
	cs_free(insn, count);
		
	rc = 0;
	cleanup:
	return rc;
}

