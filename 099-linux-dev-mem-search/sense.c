#define ADDRESS_START 0
#define ADDRESS_STOP 0x100000000

#define _GNU_SOURCE

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <sys/mman.h>

int main(int argc, char *argv[])
{
    uint64_t offset = ADDRESS_START;

    /* since this (and multiples) are provided as the offset into /dev/mem, it
     * must abide by the rules of mmap(): must be a multiple of system page size */
    size_t chunksz = 0x1000;

    int fd = open("/dev/mem", O_SYNC);
    if(fd < 0) {
        perror("open()");
        return 1;
    }

	bool state = false;

	while (offset < ADDRESS_STOP)
	{
		//printf("currently at: 0x%08llX\n", offset);

    	unsigned char *buf = mmap(NULL, chunksz, PROT_READ, MAP_PRIVATE, fd, offset);
	    if(buf == MAP_FAILED)
	    {
	    	if(state == true)
	    		printf("  end: 0x%08llX\n", offset);
	    	state = false;
	    }
		else
		{
			if(state == false)
				printf("start: 0x%08llX\n", offset);
			state = true;
			if(munmap(buf, chunksz) != 0)
			{
				perror("munmap() failed");
				printf("tried munmap(%p, 0x%X)\n", buf, chunksz);
			}
		}

		fflush(stdout);
		offset += chunksz;
	}
}
