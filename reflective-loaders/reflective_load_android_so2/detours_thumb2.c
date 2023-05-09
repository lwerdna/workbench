#include <stdio.h>
#include <string.h>
#include <sys/mman.h> // PROT_READ
#include <sys/mman.h> // PROT_READ

#include "libfake_so.h"

extern unsigned char *ashmem_data;
extern int ashmem_fd;

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
	char prot_str[128]={0};
	char flags_str[128]={0};
	uint8_t *tmp;

//	if(fd == -1)
//		while(1);

	prot_to_str(prot, prot_str);
	flags_to_str(flags, flags_str);
	printf("detour_mmap(%p, 0x%X,%s,%s, %d, 0x%X)\n", addr, len, prot_str, flags_str, fd, offset);

	if(fd != ashmem_fd) {
		printf("not our fd (=%d), bailing\n", ashmem_fd);
		tmp = mmap(addr, len, prot, flags, fd, offset);
	}
	else {
		tmp = mmap(addr, len, prot, MAP_TYPE|MAP_SHARED, fd, offset);
	}

	//printf("tmp is: 0x%08X\n", tmp);

	if(tmp == NULL)
		printf("ERROR: mmap() failed\n");
	else {
		if(fd != -1) {
			int i=0;
			for(i=0; i<8; ++i)
				printf("%02X ", tmp[i]);
			printf("\n");
		}
	}

	return tmp;
}

void *detour_mmap64(void *addr, size_t len, int prot, int flags, int fd, off64_t offset)
{
	char prot_str[128]={0};
	char flags_str[128]={0};
	uint8_t *tmp;

	prot_to_str(prot, prot_str);
	flags_to_str(flags, flags_str);
	printf("detour_mmap64(%p, 0x%X,%s,%s, %d, 0x%X)\n", addr, len, prot_str, flags_str, fd, offset);

	if(fd != ashmem_fd) {
		printf("not our fd (=%d), bailing\n", ashmem_fd);
		tmp = mmap(addr, len, prot, flags, fd, offset);
	}
	else {
		tmp = mmap(addr, len, prot, MAP_SHARED, fd, offset);
	}

	if(tmp == NULL)
		printf("ERROR: mmap64() failed\n");
	else {
		if(fd != -1) {
			int i=0;
			for(i=0; i<8; ++i)
				printf("%02X ", tmp[i]);
			printf("\n");
		}
	}

	if(len == 0x1004) {
		printf("I'm calling it!\n");
		break_me();
	}

	return tmp;
}

