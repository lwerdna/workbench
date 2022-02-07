#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

//uint32_t POLY = 0xedb88320;
//uint32_t POLY = 0xffffffff;
//uint32_t POLY = 0x82345678;
uint32_t POLY = 0x12345678;

/* https://yurichev.com/news/20211224_CRC32/ */
// copypasted from https://rosettacode.org/wiki/CRC-32#C 
uint32_t
rc_crc32(uint32_t crc, const char *buf, size_t len)
{
	static uint32_t table[256];
	static int have_table = 0;
	uint32_t rem;
	uint8_t octet;
	int i, j;
	const char *p, *q;
 
	/* This check is not thread safe; there is no mutex. */
	if (have_table == 0) {
		/* Calculate CRC table. */
		for (i = 0; i < 256; i++) {
			rem = i;  /* remainder from polynomial division */
			for (j = 0; j < 8; j++) {
				if (rem & 1) {
					rem >>= 1;
					rem ^= POLY;
				} else
					rem >>= 1;
			}
			table[i] = rem;
		}
		have_table = 1;
	}
 
	crc = ~crc;
	q = buf + len;
	for (p = buf; p < q; p++) {
		octet = *p;  /* Cast to unsigned octet. */
		crc = (crc >> 8) ^ table[(crc & 0xff) ^ octet];
	}
	return ~crc;
}

int main(int ac, char **av)
{
	#define BYTES_NEEDED (0x100000000 / 8)
	unsigned char *mem = malloc(BYTES_NEEDED); // 512mb
	memset(mem, 0, BYTES_NEEDED);

	uint32_t input = 0;

	for(input=0; 1; input++)
	{
		uint32_t result = rc_crc32(0, (const char *)&input, sizeof(uint32_t));

		if(mem[result >> 3] & (1 << (result & 7))) {
			printf("COLLISION! input %08X makes a previously produced crc %08X\n", input, result);
			exit(-1);
		}
		
		mem[result >> 3] |= (1 << (result & 7));

		if((input & 0xFFFFFF) == 0)
			printf("on %08X (%.02f%%)\n", input, 100.0 * input / 0x100000000);

		if(input == 0xFFFFFFFF)
			break;
	}

	printf("final memory sanity check:\n");
	int i;
	for(i=0; i<BYTES_NEEDED; i++)
	{
		if(mem[i] != 0xFF)
		{
			printf("mem[%d] == 0x%02X\n", i, mem[i]);
			break;
		}
	}

	printf("PASS!\n");

	return 0;
}
