/*
int add(int a, int b)
{
    return a+b;
}

int collatz_next(n)
{
	return 3*n + 1;
}
*/

#include <stdint.h>

typedef uint16_t __u16;
typedef uint32_t __u32;
typedef uint64_t __u64;
typedef int64_t __s64;

struct statx_timestamp {
    __s64 tv_sec;    /* Seconds since the Epoch (UNIX time) */
    __u32 tv_nsec;   /* Nanoseconds since tv_sec */
};

struct statx {
    __u32 stx_mask;        /* Mask of bits indicating
                              filled fields */
    __u32 stx_blksize;     /* Block size for filesystem I/O */
    __u64 stx_attributes;  /* Extra file attribute indicators */
    __u32 stx_nlink;       /* Number of hard links */
    __u32 stx_uid;         /* User ID of owner */
    __u32 stx_gid;         /* Group ID of owner */
    __u16 stx_mode;        /* File type and mode */
    __u64 stx_ino;         /* Inode number */
    __u64 stx_size;        /* Total size in bytes */
    __u64 stx_blocks;      /* Number of 512B blocks allocated */
    __u64 stx_attributes_mask;
                           /* Mask to show what's supported
                              in stx_attributes */

    /* The following fields are file timestamps */
    struct statx_timestamp stx_atime;  /* Last access */
    struct statx_timestamp stx_btime;  /* Creation */
    struct statx_timestamp stx_ctime;  /* Last status change */
    struct statx_timestamp stx_mtime;  /* Last modification */

    /* If this file represents a device, then the next two
       fields contain the ID of the device */
    __u32 stx_rdev_major;  /* Major ID */
    __u32 stx_rdev_minor;  /* Minor ID */

    /* The next two fields contain the ID of the device
       containing the filesystem where the file resides */
    __u32 stx_dev_major;   /* Major ID */
    __u32 stx_dev_minor;   /* Minor ID */
    __u64 stx_mnt_id;      /* Mount ID */
};

int statx(int dirfd, const char *restrict pathname, int flags,
          unsigned int mask, struct statx *restrict statxbuf)
{
	dirfd = 0;
	pathname = "hey";
	flags = 0;
	mask = 0;
	statxbuf->stx_mask = 0xDEADBEEF;
	return 0;
}

int magic_square(int a, int b, int c, int d, int e, int f, int g, int h, int i)
{
	/* valid ranges */
	if(a < 0 || a > 9) return -1;
	if(b < 0 || b > 9) return -1;
	if(c < 0 || c > 9) return -1;
	if(d < 0 || d > 9) return -1;
	if(e < 0 || e > 9) return -1;
	if(f < 0 || f > 9) return -1;
	if(g < 0 || g > 9) return -1;
	if(h < 0 || h > 9) return -1;
	if(i < 0 || i > 9) return -1;

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) return -1;
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) return -1;
	if(c == d || c == e || c == f || c == g || c == h || c == i) return -1;
	if(d == e || d == f || d == g || d == h || d == i) return -1;
	if(e == f || e == g || e == h || e == i) return -1;
	if(f == g || f == h || f == i) return -1;
	if(g == h || g == i) return -1;
	if(h == i) return -1;

	/* rows */
	if(a+b+c != 15) return -1;
	if(d+e+f != 15) return -1;
	if(g+h+i != 15) return -1;

	/* columns */
	if(a+d+g != 15) return -1;
	if(b+e+h != 15) return -1;
	if(c+f+i != 15) return -1;

	/* diagonals */
	if(a+e+i != 15) return -1;
	if(c+e+g != 15) return -1;

	/* success */
	return 0;
}

int whatever()
{
	magic_square(2, 7, 6, 9, 5, 1, 4, 3, 8);
}

/*
int main(int ac, char **av)
{
	return 0;
}
*/
