// gofer (n) - a person who runs errands, especially on a movie set or in an office

#include <stdio.h>
#include <stdlib.h> /* for malloc() (the real one) */
#include <string.h> /* for memcpy() */


#include "malloc.h"
#define MFAIL ((void*)(MAX_SIZE_T)) /* ideally in malloc.h, but actually not */

//static int G_VERBOSE = 0;
static int G_VERBOSE = 0;

//-----------------------------------------------------------------------------
// custom core memory
//-----------------------------------------------------------------------------
unsigned char *core_mem_base = NULL;
unsigned char *core_mem_break = NULL;
static unsigned int core_mem_sz = 0;

void *custom_sbrk(intptr_t increment)
{
	unsigned int core_mem_used = core_mem_break - core_mem_base;
	unsigned int core_mem_avail = core_mem_sz - core_mem_used;

	if(G_VERBOSE) {
		printf("custom_sbrk(increment=0x%X) used=0x%X avail=0x%X\n",
			increment, core_mem_used, core_mem_avail);
	}

	/* True if MORECORE cannot release space back to the system when given
	   negative arguments. This is generally necessary only if you are
	   using a hand-crafted MORECORE function that cannot handle negative
	   arguments. */
	if(increment < 0)
	{
		if(G_VERBOSE) {
			printf("  negative value (did you set DMORECORE_CANNOT_TRIM?), returning %d\n",
				core_mem_break, MFAIL);
			return MFAIL;
		}
	}

	/* MORECORE must not allocate memory when given argument zero, but
	   instead return one past the end address of memory from previous
	   nonzero call. */
	if(increment == 0)
	{
		if(G_VERBOSE) {
			printf("  returning %p\n", core_mem_break);
		}
		return core_mem_break;
	}

	unsigned char *previous_break = core_mem_break;

	if(increment > core_mem_avail)
	{
		if(G_VERBOSE) {
			printf("  too large, returning -1\n");
		}
		return MFAIL;
	}

	core_mem_break += increment;
	if(G_VERBOSE) {
		printf("  core_mem_break incremented to %p, returning %p\n",
			core_mem_break, previous_break);
	}
	return previous_break;
}

//-----------------------------------------------------------------------------
// API (meant to be called by python via ctypes)
//-----------------------------------------------------------------------------
//extern "C" void gofer_initialize()
void *gofer_initialize(size_t size)
{
	core_mem_sz = size;
	core_mem_base = malloc(core_mem_sz);
	memset(core_mem_base, 0, core_mem_sz);
	core_mem_break = core_mem_base;
	if(G_VERBOSE) {
	//if(1) {
		printf("gofer_initialize(0x%X)\n", size);
		printf("   core_mem_base: 0x%X\n", core_mem_base);
		printf("  core_mem_break: 0x%X\n", core_mem_break);
		printf("     core_mem_sz: 0x%X\n", core_mem_sz);
	}
	return core_mem_base;
}

void gofer_uninitialize(void)
{
	if(G_VERBOSE) {
	//if(1) {
		printf("gofer_uninitialize(%p)\n", core_mem_base);
	}

	free(core_mem_base);

	core_mem_base = NULL;
	core_mem_break = NULL;
	core_mem_sz = 0;

	dl_hard_reset();
}

//extern "C" void *gofer_malloc(size_t size)
void *gofer_malloc(size_t size)
{
	char *buf = dlmalloc(size);
	if(G_VERBOSE) {
		printf("gofer_malloc(0x%X) returns %p\n", size, buf);
	}
	return buf;
}

//extern "C" void gofer_free(void *p)
void gofer_free(void *p)
{
	if(G_VERBOSE) {
		printf("gofer_free(%p)\n", p);
	}
	dlfree(p);
}

void *gofer_memset(void *buf, unsigned char c, size_t n)
{
	if(G_VERBOSE) {
		printf("gofer_memset(%p, 0x%X, 0x%X)\n", buf, c, n);
	}
	return memset(buf, c, n);
}

void gofer_get_core(unsigned char *p)
{
	if(G_VERBOSE) {
		printf("gofer_get_core() returning 0x%X bytes\n", core_mem_sz);
	}
	memcpy(p, core_mem_base, core_mem_sz);
}

void *gofer_get_core_base(void)
{
	if(G_VERBOSE) {
		printf("gofer_get_core_base() returning %p\n", core_mem_base);
	}
	return core_mem_base;
}

void gofer_set_verbose(void)
{
	G_VERBOSE = 1;
}

void gofer_clear_verbose(void)
{
	G_VERBOSE = 0;
}
