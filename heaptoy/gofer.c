// gofer (n) - a person who runs errands, especially on a movie set or in an office

#include <stdio.h>
#include <stdlib.h> /* for malloc() (the real one) */
#include <string.h> /* for memcpy() */

#define CORE_MEM_SZ 1*1024*1024 // 1MB

#include "malloc.h"

//-----------------------------------------------------------------------------
// custom core memory
//-----------------------------------------------------------------------------
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

//-----------------------------------------------------------------------------
// API (meant to be called by python via ctypes)
//-----------------------------------------------------------------------------
//extern "C" void gofer_initialize()
void *gofer_initialize(void)
{
	core_mem_base = malloc(CORE_MEM_SZ);
	memset(core_mem_base, 0, CORE_MEM_SZ);
	core_mem_break = core_mem_base;
	core_mem_limit = core_mem_base + CORE_MEM_SZ;
	printf("gofer_initialize(): allocated core mem: [%p,%p)\n", core_mem_base, core_mem_limit);
	return core_mem_base;
}

void gofer_uninitialize(void)
{
	free(core_mem_base);
	printf("gofer_uninitialize()\n");
}

//extern "C" void *gofer_malloc(size_t size)
void *gofer_malloc(size_t size)
{
	char *buf = dlmalloc(size);
	printf("gofer_malloc(0x%X) returns %p\n", size, buf);
	return buf;
}

//extern "C" void gofer_free(void *p)
void gofer_free(void *p)
{
	printf("gofer_free(%p)\n", p);
	dlfree(p);
}

void *gofer_memset(void *buf, unsigned char c, size_t n)
{
	printf("gofer_memset(%p, 0x%X, 0x%X)\n", buf, c, n);
	return memset(buf, c, n);
}

void gofer_get_core(unsigned char *p)
{
	printf("gofer_get_core() returning 0x%X bytes\n", CORE_MEM_SZ);
	memcpy(p, core_mem_base, CORE_MEM_SZ);
}
