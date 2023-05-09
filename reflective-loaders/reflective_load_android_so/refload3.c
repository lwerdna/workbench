
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

const char *sig_fstat =
"\x07\xc0\xa0\xe1\x14\x70\x9f\xe5\x00\x00\x00\xef\x0c\x70\xa0\xe1";
const char *sig_mmap =
"\x80\xb5\x84\xb0\xdd\xe9\x06\xec\xcd\xf8\x08\xc0\x4f\xea\xec\x7c";
const char *sig_mmap64 =
"\xf0\xb5\x83\xb0\x1e\x46\xdd\xe9\x0a\x43\x0d\x46\x21\x46\x03\xf0";

/* detours from detours_thumb.c and detours_arm.c */
void *detour_mmap(void *addr, size_t len, int prot, int flags, int fd, uint32_t offset);
void *detour_mmap64(void *addr, size_t len, int prot, int flags, int fd, uint64_t offset);
int detour_fstat(int fd, struct stat *buf);

/* from libcutils */
int ashmem_create_region(const char *name, size_t size);
int ashmem_pin_region(int fd, size_t offset, size_t len);
int ashmem_set_prot_region(int fd, int prot);

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
	
unsigned char *ashmem_data = NULL;
int ashmem_fd = -1;

int main(int argc, char **argv)
{
	int i, fd_so, pagesz;
	void *handle = NULL;
	uint8_t *ld_elf, *__dl_fstat64, *__dl_mmap, *__dl_mmap64;
	int (*foo)(void);
	android_dlextinfo extinfo;
	char buf[__libfake_so_len];
	struct stat fstats;
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

	ashmem_fd = ashmem_create_region("libfake.so", __libfake_so_len);
	printf("ashmem_create_region() returns %d\n", ashmem_fd);
	if(ashmem_fd < 0)
		ERR("ashmem_create_region()");

	if(0 != ashmem_set_prot_region(ashmem_fd, PROT_READ | PROT_WRITE | PROT_EXEC))
		ERR("ashmem_set_prot_region()");

	ashmem_data = mmap(NULL, __libfake_so_len, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_SHARED, ashmem_fd, 0);
	if(!ashmem_data)
		ERR("mmap()");
	memcpy(ashmem_data, __libfake_so, __libfake_so_len);
	munmap(ashmem_data, __libfake_so_len);

	printf("asking ashmem name: ");
	if(ioctl(ashmem_fd, ASHMEM_GET_NAME, buf) == -1)
		ERR("ioctl(ASHMEM_GET_NAME)");
	printf("%s\n", buf);

	printf("asking ashmem size: ");
	i = ioctl(ashmem_fd, ASHMEM_GET_SIZE, NULL);
	if(i == -1)
		ERR("ioctl(ASHMEM_GET_SIZE)");
	printf("%d\n", i);

/*
  unsigned long long st_dev; \
  unsigned char __pad0[4]; \
  unsigned long __st_ino; \
  unsigned int st_mode; \
  unsigned int st_nlink; \
  uid_t st_uid; \
  gid_t st_gid; \
  unsigned long long st_rdev; \
  unsigned char __pad3[4]; \
  long long st_size; \
  unsigned long st_blksize; \
  unsigned long long st_blocks; \
  unsigned long st_atime; \
  unsigned long st_atime_nsec; \
  unsigned long st_mtime; \
  unsigned long st_mtime_nsec; \
  unsigned long st_ctime; \
  unsigned long st_ctime_nsec; \
  unsigned long long st_ino; \

*/
	printf("trying fstat()\n");
	if(fstat(ashmem_fd, &fstats) != 0)
		ERR("fstat()");
	printf("fstats.st_mode: 0x%X\n", fstats.st_mode);
	printf("fstats.st_nlink: %u\n", fstats.st_nlink);
	printf("fstats.st_size: %lld\n", fstats.st_size);
	printf("fstats.st_blksize: %lu\n", fstats.st_blksize);
	printf("fstats.st_blocks: %llu\n", fstats.st_blocks);

	printf("S_ISLNK: %d\n", S_ISLNK(fstats.st_mode));
	printf("S_ISREG: %d\n", S_ISREG(fstats.st_mode));
	printf("S_ISDIR: %d\n", S_ISDIR(fstats.st_mode));
	printf("S_ISCHR: %d\n", S_ISCHR(fstats.st_mode));
	printf("S_ISBLK: %d\n", S_ISBLK(fstats.st_mode));
	printf("S_ISFIFO: %d\n", S_ISFIFO(fstats.st_mode));
	printf("S_ISSOCK: %d\n", S_ISSOCK(fstats.st_mode));

	for(i=0; i<2; ++i) {
		printf("read\n");
		if(read(ashmem_fd, buf, __libfake_so_len) != __libfake_so_len)
			ERR("read()");

		printf("memcmp\n");
		if(memcmp(buf, __libfake_so, __libfake_so_len) != 0)
			ERR("memcmp()");

		printf("read\n");
		if(read(ashmem_fd, buf, __libfake_so_len) != 0)
			ERR("read() expected to return EOF");

		printf("seek\n");
		if(lseek(ashmem_fd, 0, SEEK_SET) == -1)
			ERR("lseek()");
	}

	/*
		RESOLVE/CHECK ld-elf!open
	*/
	ld_elf = find_ld();
	if(!ld_elf)
		ERR("find_ld()");

	__dl_fstat64 = ld_elf + OFFS_TO_FSTAT;
	if(0 != memcmp(__dl_fstat64, sig_fstat, 16))
		ERR("__dl_fstat64() doesn't match");

	__dl_mmap = ld_elf + OFFS_TO_MMAP;
	if(0 != memcmp(__dl_mmap, sig_mmap, 16))
		ERR("__dl_mmap() doesn't match");

	__dl_mmap64 = ld_elf + OFFS_TO_MMAP64;
	if(0 != memcmp(__dl_mmap64, sig_mmap64, 16))
		ERR("__dl_mmap64() doesn't match");

	/*
		CONSTRUCT, WRITE HOOK
	*/
	pagesz = getpagesize();

	*(uint32_t *)(hook_arm + 4) = (uint32_t)detour_fstat;
	if(mprotect(ld_elf + OFFS_TO_FSTAT_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_fstat64, hook_arm, 8);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_mmap;
	if(mprotect(ld_elf + OFFS_TO_MMAP_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_mmap, hook_thumb, 16);

	*(uint32_t *)(hook_thumb + 12) = (uint32_t)detour_mmap64;
	if(mprotect(ld_elf + OFFS_TO_MMAP64_ALIGNED, pagesz, PROT_READ|PROT_WRITE|PROT_EXEC))
		ERR("mprotect()");
	memcpy(__dl_mmap64, hook_thumb, 16);

	/*
		SET UP DLOPEN_EXT
	*/

	extinfo.flags = ANDROID_DLEXT_USE_LIBRARY_FD;
	extinfo.reserved_addr = 0;
	extinfo.reserved_size = 0;
	extinfo.relro_fd = 0;
	extinfo.library_fd = ashmem_fd;

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

