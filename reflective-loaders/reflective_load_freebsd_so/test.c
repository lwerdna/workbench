#include <stdio.h> // printf
#include <dlfcn.h>
#include <fcntl.h> // O_WRONLY
#include <stdint.h>
#include <stdlib.h>
#include <string.h> // memcpy
#include <unistd.h> // getpagesize
#include <sys/stat.h> // S_IRUSR
#include <sys/mman.h> // PROT_READ

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG "\n"); goto cleanup; }

const char *sig_open =
"\x55"
"\x48\x89\xe5"
"\x48\x81\xec\xd0\x00\x00\x00"
"\x49\x89\xca"
"\x49\x89\xd3";

uint32_t detour_open(char *path, int mode)
{
	int rc = -1;
	int len = strlen(path);

	printf("detour_open(\"%s\", 0x%X)\n", path, mode);
	return open(path, mode);

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

	shm_unlink("libfake.so");

	if(handle)
		dlclose(handle);
}

