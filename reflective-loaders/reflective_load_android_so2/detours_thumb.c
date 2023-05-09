#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <inttypes.h>
#include <sys/mman.h> // PROT_READ

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG " %s\n", strerror(errno)); goto cleanup; }

extern void dump_bytes(void *buf_, int len, uint32_t addr);

// platforms/android-26/arch-arm/usr/include/asm-generic/mman-common.h
void prot_to_str(int flags, char *str)
{
	if(flags & PROT_READ) strcat(str, " PROT_READ");
	if(flags & PROT_WRITE) strcat(str, " PROT_WRITE");
	if(flags & PROT_EXEC) strcat(str, " PROT_EXEC");
	if(flags & PROT_SEM) strcat(str, " PROT_SEM");
	if(flags & PROT_NONE) strcat(str, " PROT_NONE");
	if(flags & PROT_GROWSDOWN) strcat(str, " PROT_GROWSDOWN");
	if(flags & PROT_GROWSUP) strcat(str, " PROT_GROWSUP");
}

void flags_to_str(int flags, char *str)
{
	if(flags & MAP_SHARED) strcat(str, " MAP_SHARED");
	if(flags & MAP_PRIVATE) strcat(str, " MAP_PRIVATE");
	if(flags & MAP_TYPE) strcat(str, " MAP_TYPE");
	if(flags & MAP_FIXED) strcat(str, " MAP_FIXED");
	if(flags & MAP_ANONYMOUS) strcat(str, " MAP_ANONYMOUS");
	if(flags & MAP_UNINITIALIZED) strcat(str, " MAP_UNINITIALIZED");
}

void break_me(void)
{
	printf("I'm called!\n");
	while(0);
}

/* see platforms/android-26/arch-mips/usr/include/sys/mman.h */
void *detour_mmap(void *addr, size_t len, int prot, int flags, int fd, off_t offset)
{
	int i;
	char prot_str[128]={0};
	char flags_str[128]={0};
	uint8_t *tmp = NULL;

	if(fd != 666)
		return mmap(addr, len, prot, flags, fd, offset);

	prot_to_str(prot, prot_str);
	flags_to_str(flags, flags_str);
	printf("detour_mmap(%p, 0x%X,%s,%s, %d, 0x%X)\n", addr, len, prot_str, flags_str, fd, offset);

	if(flags & MAP_FIXED) {
		/* for fixed addresses, we abandon malloc and relay the requested
			address to mmap */
		tmp = mmap(addr, len, prot, MAP_ANONYMOUS | MAP_FIXED, -1, 0);
		memcpy(tmp, __libfake_so + offset, len);
	}
	else {
		if(len & 0xFFF) {
			len = (len & 0xFFFFF000) + 0x1000;
			printf("len rounded up to 0x%X\n", len);
		}

		tmp = malloc(len);
		if(!tmp)
			ERR("malloc()");
		memcpy(tmp, __libfake_so + offset, len);
		if(mprotect(tmp, len, prot))
			printf("mprotect() not happy\n");
	}
		
	dump_bytes(tmp, 32, (uint32_t)tmp);

	cleanup:
	return tmp;
}

void *detour_mmap64(void *addr, size_t len, int prot, int flags, int fd, off64_t offset)
{
	int i;
	char prot_str[128]={0};
	char flags_str[128]={0};
	uint8_t *tmp = NULL;

	if(fd != 666)
		return mmap(addr, len, prot, flags, fd, offset);

	prot_to_str(prot, prot_str);
	flags_to_str(flags, flags_str);
	printf("detour_mmap64(%p, 0x%X,%s,%s, %d, 0x%X)\n", addr, len, prot_str, flags_str, fd, offset);

	if(flags & MAP_FIXED) {
		/* for fixed addresses, we abandon malloc and relay the requested
			address to mmap */
		tmp = mmap(addr, len, prot, MAP_ANONYMOUS | MAP_FIXED, -1, 0);
		if(tmp == MAP_FAILED) {
			printf("mmap() failed: %s\n", strerror(errno));
			goto cleanup;
		}
		printf("mmap() returned %p\n", tmp);
		memcpy(tmp, __libfake_so + offset, len);
	}
	else {
		if(len & 0xFFF) {
			len = (len & 0xFFFFF000) + 0x1000;
			printf("len rounded up to 0x%X\n", len);
		}

		tmp = malloc(len);
		if(!tmp)
			ERR("malloc()");
		memcpy(tmp, __libfake_so + offset, len);
		if(mprotect(tmp, len, prot))
			printf("mprotect() not happy\n");
	}
		
	dump_bytes(tmp, 32, (uint32_t)tmp);

	cleanup:
	return tmp;
}

ssize_t detour_readlink_chk(char *path, char * buf, size_t len, size_t buflen)
{
	ssize_t rc = 0;
	int slen;

	printf("detour_readlink_chk(\"%s\", %p, %d, %d)\n", path, buf, len, buflen);

	slen = strlen(path);
	if(slen > 4 && strcmp(path+slen-4, "/666")==0)
		strcpy(buf, "/system/lib/libfake.so");
	else
		rc = readlink(path, buf, len, buflen);

	printf("returning \"%s\"\n", buf);
	return rc;
}

ssize_t detour_pread64(int fd, void *buf, size_t count, off64_t offset, size_t buflen)
{
	printf("detour_pread64(%d, %p, %d (0x%X), %d (%" PRIx64 "), %d (%X))\n",
		fd, buf, count, count, offset, offset, buflen, buflen);

	if(fd != 666)
		return pread64(fd, buf, count, offset);

	memcpy(buf, __libfake_so + offset, count);

	dump_bytes(buf, 32, (uint32_t)buf);

	return count;
}
