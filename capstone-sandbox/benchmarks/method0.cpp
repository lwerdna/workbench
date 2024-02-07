/* binary method0: cs_disasm() one instruction at a time
	g++ method0.cpp -o method0 -lcapstone
*/

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

#include <sys/time.h>

#include <capstone/capstone.h>

#define NUM_TESTS 1000000

int main(int ac, char **av)
{
	int i;
	bool quiet = ac > 1 && !strcmp(av[1], "quiet");

	/* timing vars */
	struct timeval tvstart, tvstop;
	double tvdelta;

	/* capstone vars */
	csh handle;
	cs_insn *insn = NULL;
	size_t count;

	/* setup */
	gettimeofday(&tvstart, NULL);
	cs_open(CS_ARCH_ARM, CS_MODE_ARM, &handle);
	gettimeofday(&tvstop, NULL);
	tvdelta = (double)(tvstop.tv_usec - tvstart.tv_usec) / 1000000;
	tvdelta += (double)tvstop.tv_sec - tvstart.tv_sec;
	if(!quiet)
		printf("setup time: %f\n", tvdelta);

	/* start */
	gettimeofday(&tvstart, NULL);
	for(i=0; i<NUM_TESTS; ++i) {
		uint32_t insword = (rand()<<16) | rand();

		count = cs_disasm(handle, (const uint8_t *)&insword, 4, 0, 1, &insn);

		if(count != 1) {
			if(cs_errno(handle) != CS_ERR_OK)
				exit(-1);

			if(!quiet)
				printf("%08X undef\n", insword);
		}
		else
		if(!quiet)
			printf("%08X %s %s\n", insword, insn->mnemonic, insn->op_str);

		if(insn)
			cs_free(insn, count);
	}
	gettimeofday(&tvstop, NULL);
	tvdelta = (double)(tvstop.tv_usec - tvstart.tv_usec) / 1000000;
	tvdelta += (double)tvstop.tv_sec - tvstart.tv_sec;
	printf("total time: %f for %d tests (%f instrs/sec)\n",
		tvdelta, NUM_TESTS, NUM_TESTS/tvdelta);

	return 0;
}

