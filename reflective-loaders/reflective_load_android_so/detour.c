#include <stdio.h> // printf
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <fcntl.h> // O_RDWR
#include <sys/mman.h> // PROT_READ
#include <linux/ashmem.h>

#include "libfake_so.h"

#define ERR(MSG) { printf("ERROR: " MSG "\n"); goto cleanup; }

// these pragma's didn't work
// #pragma push
// #pragma thumb

// target attribute must wait until GCC 6
//uint32_t detour_open(char *path, int mode) __attribute__((target("thumb")));
uint32_t detour_open(char *path, int mode)
{
	int rc = -1, i, tmp;
	int fd_shm = -1;
	int len = strlen(path);
	char buf[ASHMEM_NAME_LEN];
	struct ashmem_pin pin;
	void *data;

	printf("detour_open(\"%s\", 0x%X)\n", path, mode);

	/* return error for any calls not opening libfake.so
		we expect the linker to try /etc/ld.so.cache first */
	if(len < 17 || strcmp(path+len-17, "libalias_dummy.so"))
		goto cleanup;

	fd_shm = open("/dev/ashmem", O_RDWR);
	if(fd_shm == -1) {
		printf("strerror(): %s\n", strerror(errno));
		ERR("open(\"/dev/ashmem\")");
	}
	printf("fd of ashmem is: %d\n", fd_shm);

	// visible in /proc/pid/maps
	if(ioctl(fd_shm, ASHMEM_SET_NAME, "FOO") == -1)
		ERR("ioctl(ASHMEM_SET_NAME)");

	printf("setting ashmem size: %d\n", __libfake_so_len);
	if(ioctl(fd_shm, ASHMEM_SET_SIZE, __libfake_so_len) == -1)
		ERR("ioctl(ASHMEM_SET_SIZE)");

	data = mmap(NULL, __libfake_so_len, PROT_READ | PROT_WRITE, MAP_SHARED, fd_shm, 0);
	if(!data) {
		printf("ERROR: mmap() %s\n", strerror(errno));
		goto cleanup;
	}

	printf("mmap successful\n");

	printf("asking ashmem name: ");
	if(ioctl(fd_shm, ASHMEM_GET_NAME, buf) == -1)
		ERR("ioctl(ASHMEM_GET_NAME)");
	printf("%s\n", buf);

	printf("asking ashmem size: ");
	len = ioctl(fd_shm, ASHMEM_GET_SIZE, NULL);
	if(len == -1)
		ERR("ioctl(ASHMEM_GET_SIZE)");
	printf("%d\n", len);

//	pin.offset = 0;
//	pin.len = 0x2000;
//	if(ioctl(fd_shm, ASHMEM_PIN, &pin) == -1) {
//		printf("strerror(): %s\n", strerror(errno));
//		ERR("ioctl(ASHMEM_PIN)");
//	}
//	printf("after pin, .offset=0x%X .len=0x%X\n", pin.offset, pin.len);

	//if(ftruncate(fd_shm, __libfake_so_len) == -1)
	//	ERR("ftruncate()");

	memcpy(data, __libfake_so, __libfake_so_len);

	/*
	tmp = write(fd_shm, __libfake_so, 0x1);
	if(tmp != 0x2000) {
		printf("write() only returned %d\n", tmp);
		printf("strerror(): %s\n", strerror(errno));
		ERR("write()");
	}
	*/

	if(lseek(fd_shm, 0, SEEK_SET) == -1)
		ERR("lseek()");

	if(read(fd_shm, buf, 8) != 8) {
		ERR("read()");
	}

	for(i=0; i<8; ++i)
		printf("%02X ", buf[i] & 0xFF);
	printf("\n");

	if(lseek(fd_shm, 0, SEEK_SET) == -1)
		ERR("lseek()");

	if(read(fd_shm, buf, 8) != 8) {
		ERR("read()");
	}

	for(i=0; i<8; ++i)
		printf("%02X ", buf[i] & 0xFF);
	printf("\n");

	if(lseek(fd_shm, 0, SEEK_SET) == -1)
		ERR("lseek()");

	rc = fd_shm;

	cleanup:
	//printf("returning %d\n", rc);
	return rc;
}
// #pragma pop

