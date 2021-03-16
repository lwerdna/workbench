
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

#define PACKAGE "bfd"
#define PACKAGE_VERSION "2.30"
#include <bfd.h> // for bfd_arch_arm, etc. ~/downloads/binutils-2.30/bfd/bfd.h
#include <dis-asm.h> // for struct disassemble_info, etc. ~/downloads/binutils-2.30/include/dis-asm.h

#define DISASM_ADDRESS 0

#if defined(TARGET_SH4)
#define INSWORD_TYPE uint16_t
#define INSWORD_WIDTH 16
#else
#define INSWORD_TYPE uint32_t
#define INSWORD_WIDTH 32
#endif

int cb_fprintf(void *stream, const char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);

	//printf("cb_fprintf(stream, \"%s\")\n", fmt);

	char *built_str = (char *)stream;
	char buf[1024];
	int rc = vsnprintf(buf, sizeof(buf)-1, fmt, args);
	va_end(args);
	strcat((char *)built_str, buf);
	return rc;
}

int disasm_libopcodes(uint8_t *data, int len, uint64_t addr, char *result)
{
	disassemble_info dinfo = {0};

	/* create disassemble_info */
	init_disassemble_info(&dinfo, NULL, NULL);
	/* enum bfd_flavour in <binutils_source>/bfd/bfd.h */
	dinfo.flavour = bfd_target_unknown_flavour;
	/* architecture/machine combies, see enum bfd_architecture in <binutils_source>/bfd/bfd.h */
	#if defined(TARGET_SH4)
	dinfo.arch = bfd_arch_sh;
	dinfo.mach = bfd_mach_sh4;
	dinfo.endian = BFD_ENDIAN_BIG;
	#elif defined(TARGET_PPC)
	dinfo.arch = bfd_arch_powerpc;
	dinfo.mach = bfd_mach_ppc_750;
	dinfo.endian = BFD_ENDIAN_BIG;
	#endif
	disassemble_init_for_target(&dinfo); // reads dinfo.arch and populates extra stuff

	/* use the stream pointer as our private data
		(the buffer that fprintf() should append to) */
	dinfo.stream = (void *)result;

	/* create disassembler */
	#if defined(TARGET_SH4)
	disassembler_ftype disasm = disassembler(bfd_arch_sh, TRUE, bfd_mach_sh4, NULL);
	#elif defined(TARGET_PPC)
	disassembler_ftype disasm = disassembler(bfd_arch_powerpc, TRUE, bfd_mach_ppc_750, NULL);
	#endif
	if(!disasm) {
		printf("ERROR: disassembler() returned no function\n");
		return -1;
	}

	/* call disassembler
		will use callbacks in dinfo (like .read_memory_func, .print_addr_func, etc.)
		and the defaults are fine for this use case, see the defaults in a debugger
		or look at especially buffer_read_memory() in dis-buf.c for details */
	dinfo.fprintf_func = cb_fprintf;
	dinfo.octets_per_byte = 1;
	dinfo.buffer_vma = addr;
	dinfo.stop_vma = addr + len;
	/* source data */
	dinfo.buffer = data;
	dinfo.buffer_length = len;

	result[0] = '\0';
	disasm((bfd_vma)addr, &dinfo);

	return 0;
}

void assert(int result)
{
	if(!result) {
		printf("ERROR: assert() failed\n");
		exit(-1);
	}
}

int main(int ac, char **av)
{
	char result[1024];
	uint8_t data[128];
	int nbytes = 0;

	if(ac<2) {
		printf("supply instruction bytes\n");
		return -1;
	}

	if(!strcmp(av[1],"binary") || !strcmp(av[1],"bin")) {
		INSWORD_TYPE insword = 0;

		for(int i=2; i<ac; ++i) {
			int n = strlen(av[i]);

			for(int j=0; j<n; ++j) {
				insword <<= 1;
				if(av[i][j] == '1') {
					insword |= 1;
				}
			}
		}

#if INSWORD_WIDTH==16
		data[0] = (insword >> 8) & 0xFF;
		data[1] = insword & 0xFF;
		nbytes = 2;
#elif INSWORD_WIDTH==32
		data[0] = (insword >> 24) & 0xFF;
		data[1] = (insword >> 16) & 0xFF;
		data[2] = (insword >> 8) & 0xFF;
		data[3] = insword & 0xFF;
		nbytes = 4;
#endif
	}
	else {
		nbytes = ac - 1;
		for(int i=0; i<nbytes; ++i)
			data[i] = strtoul(av[i+1], NULL, 16);
	}

	//printf("disassembling: ");
	for(int i=0; i<nbytes; ++i) {
		printf("%02X ", data[i]);
	}

	if(disasm_libopcodes(data, nbytes, DISASM_ADDRESS, result)) {
		printf("ERROR: disasm_libopcodes()\n");
		return -1;
	}

	#define RED "\x1B[31m"
	#define NONE "\x1B[0m"
	printf(RED "%s\n" NONE, result);

	return 0;
}

