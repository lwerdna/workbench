#include <stdio.h> // printf
#include <dlfcn.h>
#include <fcntl.h> // O_WRONLY
#include <stdint.h>
#include <stdlib.h>
#include <string.h> // memcpy
#include <unistd.h> // getpagesize
#include <sys/mman.h> // PROT_READ

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG "\n"); goto cleanup; }

const char *sig_open64 =
"\xb8\x02\x00\x00\x00\x0f\x05\x48\x3d\x01\xf0\xff\xff\x73\x01\xc3";

const char *tramp_init =
"\xff\x35\x17\x00\x00\x00"			/* 00: push <tramp_prolog> */

"\xff\x35\x1F\x00\x00\x00"			/* 06: push <detour_open> */
"\xc3"								/* 0C: retq to detour_open */

									/* 0D: tramp_prolog: */
"\x89\x45\xcc"						/* 0D: mov dword ptr[rbp-0x34], eax */
"\xff\x35\x27\x00\x00\x00"			/* 10: push <hook_loc_ret> */
"\xc3"								/* 16: retq to hook_loc_ret */
"\x00\x00\x00\x00\x00\x00\x00\x00"	/* 17: <tramp_prolog> */
"\x00\x00\x00\x00\x00\x00\x00\x00"	/* 1F: <detour_open> */
"\x00\x00\x00\x00\x00\x00\x00\x00"	/* 27: <hook_loc_ret> */
;									/* 2F: */

/* from ld */
extern void _dl_debug_state(void);

uint32_t detour_open(char *path, int mode)
{
	int rc = -1;
	int len = strlen(path);

	printf("detour_open(\"%s\", 0x%X)\n", path, mode);

	/* return error for any calls not opening libfake.so
		we expect the linker to try /etc/ld.so.cache first */
	if(len < 10 || strcmp(path+len-10, "libfake.so"))
		goto cleanup;

	rc = shm_open("libfake.so", O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR); 
	if(rc < 1)
		ERR("memfd_create()");

	if(write(rc, libfake_so, libfake_so_len) != libfake_so_len)
		ERR("write()");

	if(lseek(rc, 0, SEEK_SET) == -1)
		ERR("lseek()");

	cleanup:
	//printf("returning %d\n", rc);
	return rc;
}

/* find the address of the dynamic loader

STRATEGY:
	Parse this ELF's PLT entry for LD's _dl_debug_state function, then scan
	down for ELF header. Ensure PLT entry with "-l:ld-2.19.so" at compile time.
*/
void *find_ld(void)
{
	void *retval = NULL;
	int i, pagesz, fd;
	uint8_t *p;

	/* test readability of memory by calling write() on this */
	fd = open("/dev/random", O_WRONLY);

	pagesz = getpagesize();
	//printf("page size is: %d\n", pagesz);

	/* in case of lazy loading, call once to fill PLT */
	_dl_debug_state();

	/* resolves to something like:
		0x400690 <dl_debug_state@plt>:	0xff 0x25 0xba 0x09 0x20 0x00
		where 0x2009ba is rel address in jmp QWORD PTR [rip+0x2009ba] */
	p = (void *)_dl_debug_state;
	/* effective rip is (p+6) and add the rel part */
	p = p + 6 + *(uint32_t *)(p+2);
	/* finally dereference this to an address */
	p = (void *) *(uint64_t *)p;
	//printf("libc!_dl_debug_state: %p\n", p);

	/* align */
	p = (void *) ((uint64_t)p & ~((uint64_t)pagesz-1));
	//printf("on boundary: %p\n", p);

	/* scan back */
	for(i=0; i<32; ++i) {
		//printf("testing %p\n", p);
		if(write(fd, p, 4) != -1 && *(uint32_t *)p == 0x464c457f) {
			//printf("ELF found at %p\n", p);
			retval = p;
			break;
		}

		p -= pagesz;
	}

	if(fd)
		close(fd);

	return retval;
}

int main(int argc, char **argv)
{
	int i, pagesz;
	void *handle = NULL;
	uint8_t *tramp = NULL;
	uint8_t *ld_linux_x86_64 = NULL, *open64 = NULL, *p8;
	uint8_t hook[] = {
		0xff, 0x35, 0x01, 0x00, 0x00, 0x00, 0xc3,
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
	};
	int (*foo)(void);
	double (*cos)(double);

	/*
		RESOLVE/CHECK ld-linux-x86-64!open64
	*/
	ld_linux_x86_64 = find_ld();
	if(!ld_linux_x86_64)
		ERR("find_ld()");

	open64 = ld_linux_x86_64 + 0x194d0;
	if(0 != memcmp(open64, sig_open64, 16))
		ERR("open64() doesn't match");

	/*
		CONSTRUCT TRAMPOLINE
	*/
	pagesz = getpagesize();

	tramp = (void *)aligned_alloc(pagesz, pagesz);
	if(!tramp) 
		ERR("memalign()");

	if(mprotect(tramp, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");

	memcpy(tramp, tramp_init, 0x2F);
	*(uint64_t *)(tramp + 0x17) = (uint64_t)tramp + 0x0D; /* set tramp_prolog addr */
	*(uint64_t *)(tramp + 0x1F) = (uint64_t)detour_open; /* detour addr */
	*(uint64_t *)(tramp + 0x27) = (uint64_t)open64 + 0xF; /* return after detour addr */

	/*
		CONSTRUCT, WRITE HOOK
	*/
	*(uint64_t *)(hook + 7) = (uint64_t)detour_open;

	if(mprotect(ld_linux_x86_64+0x19000, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");

	//printf("writing to %p\n", open64);
	//for(i=0; i<15; ++i)
	//	printf("%02X ", open64[i]);
	//printf("\n");

	memcpy(open64, hook, 15);

	/*
		OPEN SHARED OBJ, EXEC FUNC
	*/

	handle = dlopen("libfake.so", RTLD_NOW);
	if (!handle)
		ERR("dlopen()");

	foo = dlsym(handle, "foo");
	if(!foo)
		ERR("dlsym()");

	printf("foo() returns %d\n", foo());

	if(dlclose(handle))
		ERR("dlclose()");
	handle = NULL;

	/* unhook */
	if(open64 && 0 != memcmp(open64, sig_open64, 16))
		memcpy(open64, sig_open64, 16);

	/* test that we've cleaned up sufficiently by loading other libs */
	handle = dlopen("libm.so.6", RTLD_NOW);
	if (!handle)
		ERR("dlopen()");

	cos = dlsym(handle, "cos");
	if(!foo)
		ERR("dlsym()");

	printf("cos(0) returns %f (expect 1)\n", cos(0));
	printf("cos(pi/4 == 45*) returns %f (expect .707 == 1/sqrt(2))\n", cos(0.785398));
	printf("cos(pi/2 == 90*) returns %f (expect 0)\n", cos(1.570797));

	if(dlclose(handle))
		ERR("dlclose()");
	handle = NULL;

	/* done */

	cleanup:

	if(tramp)
		free(tramp);

	shm_unlink("libfake.so");

	if(handle)
		dlclose(handle);
}


