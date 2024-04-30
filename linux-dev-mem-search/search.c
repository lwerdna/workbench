#define ADDRESS_START 0
#define ADDRESS_STOP 0x100000000

#define SLEEP_SOMETIMES 1

#define _GNU_SOURCE

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>

// https://stackoverflow.com/questions/25969466/dump-program-in-c-language
void dump(const void* data, size_t size, off_t offset) 
{
    char ascii[17];
    size_t i, j;
    ascii[16] = '\0';
    for(i = 0; i < size; ++i)
    {
        if(i % 16 == 0)
            printf("%08lX: ", offset+i);

        printf("%02X ", ((unsigned char*)data)[i]);
        if(((unsigned char*)data)[i] >= ' ' && ((unsigned char*)data)[i] <= '~') {
            ascii[i % 16] = ((unsigned char*)data)[i];
        } else {
            ascii[i % 16] = '.';
        }
        if((i+1) % 8 == 0 || i+1 == size) {
            printf(" ");
            if((i+1) % 16 == 0) {
                printf("|  %s \n", ascii);
            } else if(i+1 == size) {
                ascii[(i+1) % 16] = '\0';
                if((i+1) % 16 <= 8) {
                    printf(" ");
                }
                for (j = (i+1) % 16; j < 16; ++j) {
                    printf("   ");
                }
                printf("|  %s \n", ascii);
            }
        }
    }
}

int main(int argc, char *argv[])
{
	uint8_t *needle = "\x01\x00\x41\x54"; // atag_header with size=5 id=0x54410001 (ATAG_CORE)
    size_t needle_len = 4;

	//uint8_t *needle = "\x42\x48\x42\x48\x7B\x0C\x7B\x0C"; // test value that comes up in my /dev/mem
    //size_t needle_len = 8;

    uint64_t offset = ADDRESS_START;
    if(argc > 1)
    	offset = strtoull(argv[1], NULL, 16);

	printf("starting at 0x%016llX\n", offset);

    /* since this (and multiples) are provided as the offset into /dev/mem, it
     * must abide by the rules of mmap(): must be a multiple of system page size */
    size_t chunksz = 0x1000;

    int fd = open("/dev/mem", O_SYNC);
    if(fd < 0) {
        perror("open()");
        return 1;
    }

	int scan_i = 0;
	while (offset < ADDRESS_STOP)
	{
		if((scan_i % 1024) == 0)
		{
			printf("currently at: 0x%08llX\n", offset);
			sleep(1);
		}
		//if((offset & 0x000FFFFF) == 0)
		//	printf("currently at: 0x%08llX\n", offset);

    	unsigned char *buf = mmap(NULL, chunksz, PROT_READ, MAP_PRIVATE, fd, offset);
	    if(buf == MAP_FAILED) {
	        perror("mmap() failed");
	        printf("tried mmap(addr=NULL, len=0x%X, prot=0x%X, flags=0x%X, fd=%d, offset=0x%llX)\n", chunksz, PROT_READ, MAP_PRIVATE, fd, offset);
	        return 1;
	    }

		//dump(buf, chunksz, offset);

		void *result = memmem(buf, chunksz, needle, needle_len);
		if(result)
		{
			size_t delta = ((uint8_t *)result - (uint8_t *)buf);
			printf("Found at 0x%llX\n", offset + delta);
			dump(buf, chunksz, offset);
		}

		if(munmap(buf, chunksz) != 0)
		{
			perror("munmap() failed");
			printf("tried munmap(%p, 0x%X)\n", buf, chunksz);
		}

		fflush(stdout);
		scan_i += 1;
		offset += chunksz;
	}
}
