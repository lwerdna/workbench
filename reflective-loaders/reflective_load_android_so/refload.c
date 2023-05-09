
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

  export LD_DEBUG=2 (see header of linker/linker_debug.h), watch with `adb logcat`

b __dl___strerror_lookup

*/

#include <stdio.h> // printf
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h> // O_WRONLY
#include <stdint.h>
#include <stdlib.h>
#include <string.h> // memcpy
#include <unistd.h> // getpagesize
#include <sys/stat.h> // S_IRUSR, fstat()
#include <sys/mman.h> // PROT_READ

#include <linux/ashmem.h>

#include <android/dlext.h>

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG " %s\n", strerror(errno)); goto cleanup; }

#define OFFS_TO_OPEN 0x3D374
#define OFFS_TO_OPEN_ALIGNED 0x3D000
#define OFFS_TO_FSTAT 0x458CC
#define OFFS_TO_FSTAT_ALIGNED 0x45000
#define OFFS_TO_MMAP 0x3EBE8
#define OFFS_TO_MMAP_ALIGNED 0x3E000
#define OFFS_TO_MMAP64 0x3EB3C
#define OFFS_TO_MMAP64_ALIGNED 0x3E000
#define OFFS_TO_PREAD64 0x46d78
#define OFFS_TO_PREAD64_ALIGNED 0x46000
#define OFFS_TO_READLINK 0x46DDC
#define OFFS_TO_READLINK_ALIGNED 0x46000

const char *sig_readlink_chk =
"\x80\xb5\x9a\x42\x0b\xd8\xb2\xf1\xff\x3f\xc4\xbf\xbd\xe8\x80\x40";
const char *sig_fstat =
"\x07\xc0\xa0\xe1\x14\x70\x9f\xe5\x00\x00\x00\xef\x0c\x70\xa0\xe1";
const char *sig_mmap =
"\x80\xb5\x84\xb0\xdd\xe9\x06\xec\xcd\xf8\x08\xc0\x4f\xea\xec\x7c";
const char *sig_mmap64 =
"\xf0\xb5\x83\xb0\x1e\x46\xdd\xe9\x0a\x43\x0d\x46\x21\x46\x03\xf0";
const char *sig_pread64 =
"\x80\xb5\x04\x9b\x9a\x42\x0b\xd8\xb2\xf1\xff\x3f\xc4\xbf\xbd\xe8";

/* detours from detours_thumb.c and detours_arm.c */
void *detour_mmap(void *addr, size_t len, int prot, int flags, int fd, uint32_t offset);
void *detour_mmap64(void *addr, size_t len, int prot, int flags, int fd, uint64_t offset);
ssize_t detour_pread64(int fd, void * buf, size_t nbytes, off64_t offset, size_t buflen);
int detour_fstat(int fd, struct stat *buf);
ssize_t detour_readlink_chk(char *p, char * buf, size_t len, size_t buflen);

/* byte dumper */
void dump_bytes(void *buf_, int len, uint32_t addr)
{
    int i, j;
    char ascii[17];
	uint8_t *buf = buf_;

    i = 0;
    while(i < len) {
        printf("%08X: ", addr);
       
        for(j=0; j<16; ++j) {

            if(i < len) {
                printf("%02X ", buf[i]);
    
                if((buf[i] >= ' ') && (buf[i] < '~'))
                    ascii[j] = buf[i];
                else
                    ascii[j] = '.';
            }
            else {
                printf("   ");
                ascii[j] = ' ';
            }

            i++;
        }
        ascii[sizeof(ascii)-1] = '\0';

        printf(" %s\n", ascii);
        addr += 16;
    }
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
	int i, fd_so, pagesz;
	void *handle = NULL;
	uint8_t *ld_elf, *__dl_fstat64, *__dl_mmap, *__dl_mmap64, *__dl_pread64, *__dl_readlink_chk;
	int (*foo)(void);
	android_dlextinfo extinfo;
	char buf[__libfake_so_len];
	uint8_t hook_arm[] = {
		0x04, 0xf0, 0x1f, 0xe5,	// ldr pc, [pc, #-4]
		0x00, 0x00, 0x00, 0x00,	// <addr>
	};
	uint8_t hook_thumb[] = {
		0x01, 0xb4,				// push {r0}
		0x01, 0xb4,				// push {r0}
		0x01, 0x48,				// ldr r0, [pc, #4]
		0x01, 0x90,				// str r0, [sp, #4]
		0x01, 0xbc,				// pop {r0}
		0x00, 0xbd,				// pop {pc}
		0x00, 0x00, 0x00, 0x00,	// <addr>
	};

	/*
		RESOLVE/CHECK ld-elf!open
	*/
	ld_elf = find_ld();
	if(!ld_elf)
		ERR("find_ld()");

	__dl_readlink_chk = ld_elf + OFFS_TO_READLINK;
	if(0 != memcmp(__dl_readlink_chk, sig_readlink_chk, 16))
		ERR("__dl_readlink_chk() doesn't match");

	__dl_fstat64 = ld_elf + OFFS_TO_FSTAT;
	if(0 != memcmp(__dl_fstat64, sig_fstat, 16))
		ERR("__dl_fstat64() doesn't match");

	__dl_mmap = ld_elf + OFFS_TO_MMAP;
	if(0 != memcmp(__dl_mmap, sig_mmap, 16))
		ERR("__dl_mmap() doesn't match");

	__dl_mmap64 = ld_elf + OFFS_TO_MMAP64;
	if(0 != memcmp(__dl_mmap64, sig_mmap64, 16))
		ERR("__dl_mmap64() doesn't match");

	__dl_pread64 = ld_elf + OFFS_TO_PREAD64;
	if(0 != memcmp(__dl_pread64, sig_pread64, 16))
		ERR("__dl_pread64() doesn't match");

	/*
		CONSTRUCT, WRITE HOOK
	*/
	pagesz = getpagesize();

	*(uint32_t *)(hook_arm + 4) = (uint32_t)detour_fstat;
	if(mprotect(ld_elf + OFFS_TO_FSTAT_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_fstat64, hook_arm, 8);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_readlink_chk;
	if(mprotect(ld_elf + OFFS_TO_READLINK_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_readlink_chk, hook_thumb, 16);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_mmap;
	if(mprotect(ld_elf + OFFS_TO_MMAP_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_mmap, hook_thumb, 16);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_mmap64;
	if(mprotect(ld_elf + OFFS_TO_MMAP64_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_mmap64, hook_thumb, 16);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_pread64;
	if(mprotect(ld_elf + OFFS_TO_PREAD64_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_pread64, hook_thumb, 16);

	/*
		SET UP DLOPEN_EXT
	*/

	extinfo.flags = ANDROID_DLEXT_USE_LIBRARY_FD;
	extinfo.reserved_addr = 0;
	extinfo.reserved_size = 0;
	extinfo.relro_fd = 0;
	extinfo.library_fd = 666;

	//extinfo.library_fd = open("libfake.so", O_RDWR);

	/*
		OPEN SHARED OBJ, EXEC FUNC
	*/
	handle = android_dlopen_ext("libfake.so", RTLD_NOW, &extinfo);
	if (!handle)
		ERR("dlopen()");

	foo = dlsym(handle, "foo");
	if(!foo)
		ERR("dlsym()");

	printf("foo() returns %d\n", foo());

	cleanup:
	if(handle)
		dlclose(handle);
}

