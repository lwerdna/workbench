/* a shared object that can be called easily with python+ctypes */

/* */
#include <stdint.h>
#include <string.h>

/* c++ stuff */
#include <map>
#include <string>
#include <vector>
#include <iostream>

/* capstone stuff */
#include <capstone/capstone.h>
#include <capstone/arm.h>

const char *cs_err_to_string(cs_err e)
{
	switch(e) {
		case CS_ERR_OK: return "CS_ERR_OK";
		case CS_ERR_MEM: return "CS_ERR_MEM";
		case CS_ERR_ARCH: return "CS_ERR_ARCH";
		case CS_ERR_HANDLE: return "CS_ERR_HANDLE";
		case CS_ERR_CSH: return "CS_ERR_CSH";
		case CS_ERR_MODE: return "CS_ERR_MODE";
		case CS_ERR_OPTION: return "CS_ERR_OPTION";
		case CS_ERR_DETAIL: return "CS_ERR_DETAIL";
		case CS_ERR_MEMSETUP: return "CS_ERR_MEMSETUP";
		case CS_ERR_VERSION: return "CS_ERR_VERSION";
		case CS_ERR_DIET: return "CS_ERR_DIET";
		case CS_ERR_SKIPDATA: return "CS_ERR_SKIPDATA";
		case CS_ERR_X86_ATT: return "CS_ERR_X86_ATT";
		case CS_ERR_X86_INTEL: return "CS_ERR_X86_INTEL";
		default: return "WTF";
	}
}

extern "C"
int
get_disasm_capstone(uint8_t *data, int len, char *result)
{
	int rc = -1;

	static csh handle; /* capstone handle is typedef'd size_t */
	static bool init = false;

	if (!init) {
		/* initialize capstone handle */
		cs_mode mode = (cs_mode)(CS_MODE_MIPS32);

		if(cs_open(CS_ARCH_MIPS, mode, &handle) != CS_ERR_OK) {
			printf("ERROR: cs_open()\n");
			goto cleanup;
		}
		init = true;
	}

	cs_insn *insn; /* detailed instruction information
				cs_disasm() will allocate array of cs_insn here */
	size_t count;

	count = cs_disasm(handle, data,
		/* code_size */ len,
		/* address */ 0,
		/* instr count */ 1,
		/* result */ &insn
	);

	if(count != 1) {
		cs_err e;
		e = cs_errno(handle);

		if(e == CS_ERR_OK) {
			if(result)
				strcpy(result, "undefined");
		}
		else {
			printf("ERROR: cs_disasm() returned %zu cs_err=%d (%s)\n",
				count, e, cs_err_to_string(e));

			goto cleanup;
		}
	}
	else {
		if(result) {
			strcpy(result, insn->mnemonic);
			strcat(result, " ");
			strcat(result, insn->op_str);
		}
		cs_free(insn, count);
	}

	rc = 0;
	cleanup:
	return rc;
}

