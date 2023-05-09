
/*

#0  0xb6fd7374 in __dl_open64 () from target:/system/bin/linker
#1  0xb6fa5760 in __dl__ZL21open_library_on_pathsP15ZipArchiveCachePKcPxRKNSt3__16vectorINS4_12basic_stringIcNS4_11char_traitsIcEENS4_9allocatorIcEEEENS9_ISB_EEEEPSB_ () from target:/system/bin/linker
#2  0xb6fa3d30 in __dl__ZL14find_librariesP19android_namespace_tP6soinfoPKPKcjPS2_PNSt3__16vectorIS2_NS8_9allocatorIS2_EEEEjiPK17android_dlextinfob () from target:/system/bin/linker
#3  0xb6f9eb0e in __dl__ZL12find_libraryP19android_namespace_tPKciPK17android_dlextinfoP6soinfo () from target:/system/bin/linker
#4  0xb6f9ea14 in __dl__Z9do_dlopenPKciPK17android_dlextinfoPv () from target:/system/bin/linker
#5  0xb6f9cc00 in __dl__ZL10dlopen_extPKciPK17android_dlextinfoPv () from target:/system/bin/linker
#6  0x2a000c00 in main (argc=1, argv=0xbefffb34) at refload.c:141

NOTES:
  adb push /Users/andrewl/android-ndk-r15c//prebuilt/android-arm/gdbserver /data/local/tmp
  adb forward tcp:12345 tcp:5039
  adb forward --list
  adb forward --remove-all
  ./gdbserver :5034 refload
  alias gdbndk=/Users/andrewl/android-ndk-r15c//prebuilt/darwin-x86_64/bin/gdb
  target remote localhost:12345
  gdbndk --init-command command.gdb
  set arm force-mode thumb
  info sharedlibrary

  export LD_DEBUG=2 (see header of linker/linker_debug.h)
*/

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

#define ERR(MSG) { printf("ERROR: " MSG "\n"); goto cleanup; }

#define OFFS_TO_OPEN 0x3D374
#define OFFS_TO_OPEN_ALIGNED 0x3D000

/* valid for 10.2 and 10.3 */
const char *sig_open =
"\x82\xb0\x80\xb5\x82\xb0\x84\x46\x13\x48\xcd\xe9\x04\x23\x11\xf0"
"\x40\x0f\x78\x44\x00\x68\x00\x68\x01\x90\x01\xd1\x00\x23\x06\xe0";

uint32_t detour_open(char *path, int mode);

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

	/* resolves immediately to dlopen+1 */
	p = (void *)dlopen;
	printf("libc!dlopen: %p\n", p);

	/* align */
	p = (void *) ((uint32_t)p & ~((uint32_t)pagesz-1));
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
		0x00, 0x49, 0x8f, 0x46,
		0x00, 0x00, 0x00, 0x00,
	};
	int (*foo)(void);
	double (*cos)(double);

	printf("Hello, world!\n");

	/*
		RESOLVE/CHECK ld-elf!open
	*/
	ld_elf = find_ld();
	if(!ld_elf)
		ERR("find_ld()");

	open = ld_elf + OFFS_TO_OPEN;

	for(i=0; i<8; ++i)
		printf("%02X ", open[i]);
	printf("\n");

	if(0 != memcmp(open, sig_open, 32))
		ERR("open() doesn't match");

	/*
		CONSTRUCT, WRITE HOOK
	*/
	pagesz = getpagesize();

	*(uint32_t *)(hook + 4) = (uint32_t)detour_open;

	if(mprotect(ld_elf + OFFS_TO_OPEN_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");

	printf("writing to %p\n", open);
	for(i=0; i<8; ++i)
		printf("%02X ", open[i]);
	printf("\n");

	memcpy(open, hook, 8);

	for(i=0; i<8; ++i)
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
	if(open && 0 != memcmp(open, sig_open, 32))
		memcpy(open, sig_open, 32);

	/* test that we've cleaned up sufficiently by loading other libs */
legit:
	printf("LEGIT!\n");
	handle = dlopen("/system/lib/libm.so", RTLD_NOW);
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

	//shm_unlink("/shm_fake");

	if(handle)
		dlclose(handle);
}

