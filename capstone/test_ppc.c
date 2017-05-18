/* */
#include <stdint.h>

/* autils stuff */
#include <autils/parsing.h>

/* capstone stuff /usr/local/include/capstone */
#include <capstone/capstone.h>
#include <capstone/ppc.h>

char *cs_err_tostr(int err)
{
	switch(err) {
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
		default: return "UNKNOWN";
	}
}

char *ppc_grp_tostr(int grp)
{
	switch(grp) {
		case PPC_GRP_ALTIVEC: return "PPC_GRP_ALTIVEC";
		case PPC_GRP_MODE32: return "PPC_GRP_MODE32";
		case PPC_GRP_MODE64: return "PPC_GRP_MODE64";
		case PPC_GRP_BOOKE: return "PPC_GRP_BOOKE";
		case PPC_GRP_NOTBOOKE: return "PPC_GRP_NOTBOOKE";
		case PPC_GRP_SPE: return "PPC_GRP_SPE";
		case PPC_GRP_VSX: return "PPC_GRP_VSX";
		case PPC_GRP_E500: return "PPC_GRP_E500";
		case PPC_GRP_PPC4XX: return "PPC_GRP_PPC4XX";
		case PPC_GRP_PPC6XX: return "PPC_GRP_PPC6XX";
		default: return "UNKNOWN";
	}
}

int disasm_verbose(uint8_t *code, int len)
{
	int rc = -1;

    csh handle; /* capstone handle is typedef'd size_t */
    cs_insn *insn; /* detailed instruction information 
                    cs_disasm() will allocate array of cs_insn here */
    size_t nInstr; /* number of instructions disassembled
                    (number of cs_insn allocated) */

    /* initialize capstone handle */
    if(cs_open(
		CS_ARCH_PPC, /* arch */
		CS_MODE_BIG_ENDIAN, /* hardware mode (CS_MODE_*) */
		&handle /* pointer to received handle */
	  ) != CS_ERR_OK) {
        printf("ERROR: cs_open()\n");
        goto cleanup;
    }

	cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);
	//cs_option(handle, CS_OPT_DETAIL, CS_OPT_OFF);
	for(int i=0; i<len; ++i) {
		int j, nInstr;
		cs_detail *detail;
		cs_ppc *pdets;

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

		/* the bytes */
		for(int j=0; j<insn->size; ++j) 
			printf("%02X ", code[i+j]);
		/* the instruction text */
		printf(":  %s %s\n", insn->mnemonic, insn->op_str);

		/* instruction detail 
			all architecures have:
			- regs_read[]
			- regs_write[]
			- groups[] 
			then there is union per-architecture (cs_x86, cs_arm64, cs_ppc, etc.)
		*/
		detail = insn->detail;
		printf("  regs read:");
		for(j=0; j<detail->regs_read_count; ++j) {
			printf(" %s", cs_reg_name(handle, detail->regs_read[j]));
		}
		printf("\n");
		printf("  regs write:");
		for(j=0; j<detail->regs_write_count; ++j) {
			printf(" %s", cs_reg_name(handle, detail->regs_write[j]));
		}
		printf("\n");
		printf("  groups:");
		for(j=0; j<detail->groups_count; ++j) {
			int group = detail->groups[j];
			printf(" %d(%s)", group, cs_group_name(handle, group));
		}
		printf("\n");
		
		/* now the platform-specific parts */
		pdets = (cs_ppc *)&(detail->ppc);

		if(1 /* branch instruciton */) {
			printf("  branch code: %d\n", pdets->bc); // PPC_BC_LT, PPC_BC_LE, etc.
			printf("  branch hint: %d\n", pdets->bh); // PPC_BH_PLUS, PPC_BH_MINUS
		}

		printf("  update_cr0: %d\n", pdets->update_cr0);

		for(j=0; j<pdets->op_count; ++j) {
			printf("  operand%d: ", j);

			// .op_count is number of operands
			// .operands[] is array of cs_ppc_op
			cs_ppc_op op = pdets->operands[j];

		 	switch(op.type) {
				case PPC_OP_INVALID:
					printf("invalid\n");
					break;
				case PPC_OP_REG:
					printf("reg: %s\n", cs_reg_name(handle, op.reg));
					break;
				case PPC_OP_IMM:
					printf("imm: 0x%X\n", op.imm);
					break;
				case PPC_OP_MEM:
					printf("mem (%s + 0x%X)\n", cs_reg_name(handle, op.mem.base),
						op.mem.disp);
					break;
				case PPC_OP_CRX:
					printf("crx (scale:%d, reg:%s)\n", op.crx.scale, 
						cs_reg_name(handle, op.crx.reg));
					break;
				default:
					printf("unknown (%d)\n", op.type);
					break;
			}
		}

		/* done */
        cs_free(insn, nInstr);
		i += insn->size;
	}

	rc = 0;
	cleanup:
	if(rc) {
		int errno = cs_errno(handle);
		printf("cs_errno(): %d (%s)\n", errno, cs_err_tostr(errno));
	} 
    return rc;
}

int main(int ac, char **av)
{
    int rc = -1;

	if(ac > 1) {
		uint8_t code[128];
		parse_byte_list(av + 1, ac - 1, code);
		printf("disassembling bytes:");
		for(int i=0; i<ac-1; ++i)
			printf(" %02X", code[i]);
		printf("\n");
		rc = disasm_verbose(code, ac-1);
	}
	else {	
	    uint8_t code[] = {
			0x94, 0x21, 0xff, 0xe0, 
			0x7c, 0x08, 0x02, 0xa6, 
			0x90, 0x01, 0x00, 0x24, 
			0x93, 0xe1, 0x00, 0x1c, 
			0x7c, 0x3f, 0x0b, 0x78, 
			0x90, 0x7f, 0x00, 0x0c, 
			0x90, 0x9f, 0x00, 0x08, 
			0x3d, 0x20, 0x10, 0x00, 
			0x38, 0x69, 0x07, 0x74, 
			0x48, 0x00, 0x01, 0x91, 
			0x39, 0x20, 0x00, 0x00,
			0x7d, 0x23, 0x4b, 0x78, 
			0x39, 0x7f, 0x00, 0x20, 
			0x80, 0x0b, 0x00, 0x04, 
			0x7c, 0x08, 0x03, 0xa6, 
			0x83, 0xeb, 0xff, 0xfc, 
			0x7d, 0x61, 0x5b, 0x78, 
			0x4e, 0x80, 0x00, 0x20,
			0x94, 0x21, 0xff, 0xf0, 
			0x3d, 0x60, 0x10, 0x02,
			0x7c, 0x08, 0x03, 0xa6,
			0x40, 0x9c, 0x00, 0x2c
		};

		rc = disasm_verbose(code, sizeof(code));
	}
        
    return rc;
}

