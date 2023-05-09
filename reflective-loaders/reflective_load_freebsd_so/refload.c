#include <stdio.h> // printf
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h> // O_WRONLY
#include <stdint.h>
#include <stdlib.h>
#include <string.h> // memcpy
#include <unistd.h> // getpagesize
#include <sys/stat.h> // S_IRUSR
#include <sys/mman.h> // PROT_READ

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG "\n"); goto cleanup; }

#define OFFS_TO_OPEN_10_2 0x114b0
#define OFFS_TO_OPEN_ALIGNED_10_2 0x11000
#define OFFS_TO_OPEN_10_3 0x11060
#define OFFS_TO_OPEN_ALIGNED_10_3 0x11000

/* valid for 10.2 and 10.3 */
const char *sig_open =
"\x55"
"\x48\x89\xe5"
"\x48\x81\xec\xd0\x00\x00\x00"
"\x49\x89\xca"
"\x49\x89\xd3";

uint32_t detour_open(char *path, int mode)
{
	int rc = -1, tmp;
	int fd_shm;
	int len = strlen(path);

	printf("detour_open(\"%s\", 0x%X)\n", path, mode);

	/* return error for any calls not opening libfake.so
		we expect the linker to try /etc/ld.so.cache first */
	if(len < 17 || strcmp(path+len-17, "libalias_dummy.so"))
		goto cleanup;

	fd_shm = shm_open("/shm_fake", O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR); 
	if(fd_shm == -1) {
		printf("strerror(): %s\n", strerror(errno));
		ERR("shm_open()");
	}

	if(ftruncate(fd_shm, libfake_so_len) == -1)
		ERR("ftruncate()");

	tmp = write(fd_shm, libfake_so, libfake_so_len);
	if(tmp != libfake_so_len) {
		printf("write() only returned %d\n", tmp);
		printf("strerror(): %s\n", strerror(errno));
		ERR("write()");
	}

	if(lseek(fd_shm, 0, SEEK_SET) == -1)
		ERR("lseek()");

	rc = fd_shm;

	cleanup:
	//printf("returning %d\n", rc);
	return rc;
}

/* find the address of the dynamic loader

STRATEGY:
	Parse this ELF's PLT entry for LD's dlopen function, then scan
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
	printf("page size is: 0x%X\n", pagesz);

	/* in case of lazy loading, call once to fill PLT */
	dlopen("", 0);

	/* resolves to something like:
		0x400690 <dlopen@plt>:	0xff 0x25 0xba 0x09 0x20 0x00
		where 0x2009ba is rel address in jmp QWORD PTR [rip+0x2009ba] */
	p = (void *)dlopen;
	/* effective rip is (p+6) and add the rel part */
	p = p + 6 + *(uint32_t *)(p+2);
	/* finally dereference this to an address */
	p = (void *) *(uint64_t *)p;
	printf("libc!dlopen: %p\n", p);

	/* align */
	p = (void *) ((uint64_t)p & ~((uint64_t)pagesz-1));
	printf("on boundary: %p\n", p);

	/* scan back */
	for(i=0; i<32; ++i) {
		printf("testing %p\n", p);
		if(write(fd, p, 4) != -1 && *(uint32_t *)p == 0x464c457f) {
			printf("ELF found at %p\n", p);
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
	uint8_t *ld_elf = NULL, *open = NULL, *p8;
	uint8_t hook[] = {
		0xff, 0x35, 0x01, 0x00, 0x00, 0x00, 0xc3,
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
	};
	int (*foo)(void);
	double (*cos)(double);

	/*
		RESOLVE/CHECK ld-elf!open
	*/
	ld_elf = find_ld();
	if(!ld_elf)
		ERR("find_ld()");

	open = ld_elf + OFFS_TO_OPEN_10_3;

	for(i=0; i<15; ++i)
		printf("%02X ", open[i]);
	printf("\n");

	if(0 != memcmp(open, sig_open, 17))
		ERR("open() doesn't match");

	/*
		CONSTRUCT, WRITE HOOK
	*/
	pagesz = getpagesize();

	*(uint64_t *)(hook + 7) = (uint64_t)detour_open;

	if(mprotect(ld_elf + OFFS_TO_OPEN_ALIGNED_10_3, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");

	printf("writing to %p\n", open);
	for(i=0; i<15; ++i)
		printf("%02X ", open[i]);
	printf("\n");

	memcpy(open, hook, 15);

	for(i=0; i<15; ++i)
		printf("%02X ", open[i]);
	printf("\n");

	/*
		OPEN SHARED OBJ, EXEC FUNC
	*/
	handle = dlopen("libalias_dummy.so", RTLD_NOW);
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
	if(open && 0 != memcmp(open, sig_open, 17))
		memcpy(open, sig_open, 17);

	/* test that we've cleaned up sufficiently by loading other libs */
legit:
	printf("LEGIT!\n");
	handle = dlopen("libm.so.5", RTLD_NOW);
	if (!handle)
		ERR("dlopen()");
	printf("WTF?\n");
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

	shm_unlink("/shm_fake");

	if(handle)
		dlclose(handle);
}

