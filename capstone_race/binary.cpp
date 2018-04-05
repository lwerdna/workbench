
/* */
#include <stdio.h>
#include <stdint.h>

/* c++ stuff */
#include <string>
using namespace std;

/* capstone stuff */
#include <capstone/capstone.h>

/*****************************************************************************/
/* capstone */
/*****************************************************************************/
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

int disasm(uint8_t *data, uint32_t addr, string& result, string& err)
{
	int rc = -1;
	static bool init = false;

	/* capstone vars */
	static csh handle;
	cs_insn *insn = NULL;
	size_t count;

	if (!init) {
		/* initialize capstone handle */
		cs_mode mode = (cs_mode)(CS_MODE_MIPS32 | CS_MODE_BIG_ENDIAN);

		if(cs_open(CS_ARCH_MIPS, mode, &handle) != CS_ERR_OK) {
			printf("ERROR: cs_open()\n");
			goto cleanup;
		}
		init = true;
	}

	count = cs_disasm(handle, data,
		/* code_size */ 4,
		/* address */ addr,
		/* instr count */ 1,
		/* result */ &insn
	);

	if(count != 1) {
		cs_err e = cs_errno(handle);

		if(e == CS_ERR_OK) {
			result = "undefined";
		}
		else {
			char msg[128];
			sprintf(msg, "ERROR: cs_disasm() returned %zu cs_err=%d (%s)\n",
				count, e, cs_err_to_string(e));
			err = msg;
			goto cleanup;
		}
	}
	else {
		result = insn->mnemonic;
		result += " ";
		result += insn->op_str;
	}

	rc = 0;
	cleanup:
	if(insn) cs_free(insn, count);
	return rc;
}

/*****************************************************************************/
/* main */
/*****************************************************************************/

int main(int ac, char **av)
{
	#define instrWordMax 0x100000
	string result, error;

	for(uint32_t instrWord = 0; instrWord < instrWordMax+1; ++instrWord) {
		disasm((uint8_t *)&instrWord, 0, result, error);
		printf("%08X %s\n", instrWord, result.c_str());
	}
}
