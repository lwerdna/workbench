#include <stdio.h>
#include <sys/stat.h> // S_IRUSR, fstat()

#include "libfake_so.h"

int detour_fstat(int fd, struct stat *buf)
{
	struct stat *fstats;

	printf("%s()\n", __func__);

	if(fd != 0x29a)
		return fstat(fd, buf);

	/* platforms/android-24/arch-arm/usr/include/sys/stat.h */
	uint8_t saved_fstats = {
		0x01, 0xFE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0xEE, 0x1A, 0x05, 0x00,
		0xFF, 0x81, 0x00, 0x00,
		0x01, 0x00, 0x00, 0x00, /* st_nlink */
		0xD0, 0x07, 0x00, 0x00, /* st_uid */
		0xD0, 0x07, 0x00, 0x00, /* st_gid */
		0x00, 0x00, 0x00, 0x00, 
		0x00, 0x00, 0x00, 0x00,	0x00, 0x00, 0x00, 0x00, /* st_rdev */
		0x00, 0x00, 0x00, 0x00,	/* pad3 */
		0x50, 0x1A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* st_size */
		0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0xB9, 0x1F, 0x82, 0x59, 0x00, 0x00, 0x00, 0x00,
		0xB9, 0x1F, 0x82, 0x59, 0x00, 0x00, 0x00, 0x00,
		0xCF, 0x1F, 0x82, 0x59, 0x87, 0x3F, 0x82, 0x37,
		0xEE, 0x1A, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00
	};

	memcpy(buf, saved_fstats, sizeof(struct stat));
	return 0;

	if(fstat(fd, buf) != 0)
		return -1;

	printf("setting size to %d\n", __libfake_so_len);
	buf->st_size = __libfake_so_len;

	if(S_ISDIR(buf->st_mode) || S_ISCHR(buf->st_mode)) {
		printf("setting it to a regular file\n");
		buf->st_mode ^= S_IFDIR;
		buf->st_mode |= S_IFREG;
	}

	fstats = (struct stat *)saved_fstats;

	dump_bytes(fstats, struct stat, 0);

	printf("fstats->st_mode: 0x%X\n", fstats->st_mode);
	printf("fstats->st_nlink: %u\n", fstats->st_nlink);
	printf("fstats->st_size: %lld\n", fstats->st_size);
	printf("fstats->st_blksize: %lu\n", fstats->st_blksize);
	printf("fstats->st_blocks: %llu\n", fstats->st_blocks);

	printf("S_ISLNK: %d\n", S_ISLNK(fstats->st_mode));
	printf("S_ISREG: %d\n", S_ISREG(fstats->st_mode));
	printf("S_ISDIR: %d\n", S_ISDIR(fstats->st_mode));
	printf("S_ISCHR: %d\n", S_ISCHR(fstats->st_mode));
	printf("S_ISBLK: %d\n", S_ISBLK(fstats->st_mode));
	printf("S_ISFIFO: %d\n", S_ISFIFO(fstats->st_mode));
	printf("S_ISSOCK: %d\n", S_ISSOCK(fstats->st_mode));

	return 0;
}
