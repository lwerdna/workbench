#include <stdio.h>
#include <stdlib.h>

#include "malloc.h"

unsigned char *core_mem_base = NULL;
unsigned char *core_mem_break = NULL;
unsigned char *core_mem_limit = NULL;

void *custom_sbrk(intptr_t increment)
{
	unsigned int core_mem_used = core_mem_break - core_mem_base;
	unsigned int core_mem_avail = core_mem_limit - core_mem_break;

	printf("custom_sbrk(increment=0x%X) used=0x%X avail=0x%X\n",
		increment, core_mem_used, core_mem_avail);

	/* True if MORECORE cannot release space back to the system when given
	   negative arguments. This is generally necessary only if you are
	   using a hand-crafted MORECORE function that cannot handle negative
	   arguments. */
	if(increment < 0)
	{
		printf("  negative value (did you set DMORECORE_CANNOT_TRIM?), returning -1\n", core_mem_break);
		return -1;
	}

	/* MORECORE must not allocate memory when given argument zero, but
	   instead return one past the end address of memory from previous
	   nonzero call. */
	if(increment == 0)
	{
		printf("  returning %p\n", core_mem_break);
		return core_mem_break;
	}

	unsigned char *previous_break = core_mem_break;

	if(core_mem_break + increment >= core_mem_limit)
	{
		printf("  too large, returning -1\n");
		return -1;
	}

	core_mem_break += increment;
	printf("  core_mem_break incremented to %p, returning %p\n",
		core_mem_break, previous_break);
	return previous_break;
}

int main(int ac, char **av)
{
	printf("main() here\n");

	//#define CORE_MEM_SZ 16*1024*1024 // 16MB
	#define CORE_MEM_SZ 1*1024*1024 // 1MB
	core_mem_base = malloc(CORE_MEM_SZ);
	core_mem_break = core_mem_base;
	core_mem_limit = core_mem_base + CORE_MEM_SZ;
	printf("allocated core mem: [%p,%p)\n", core_mem_base, core_mem_limit);

	char *buf0 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf0);

	char *buf1 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf1);

	char *buf2 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf2);
	dlfree(buf2);

	char *buf3 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf3);
	dlfree(buf3);

	char *buf4 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf4);

	char *buf5 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf5);
	dlfree(buf5);

	char *buf6 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf6);

	char *buf7 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf7);

	char *buf8 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf8);
	dlfree(buf8);

	char *buf9 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf9);

	char *buf10 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf10);

	char *buf11 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf11);

	char *buf12 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf12);

	char *buf13 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf13);
	dlfree(buf13);

	char *buf14 = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf14);
}
