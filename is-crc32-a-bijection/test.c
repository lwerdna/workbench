// tool to calculate CRC-32/ISO-HDLC on 4-byte input values with given polynomial
//
// {'name':'CRC-32/ISO-HDLC', 'width':32, 'poly':0x04c11db7, 'init':0xffffffff, 'refin':True, 'refout':True, 'xorout':0xffffffff},
// default polynomial used here: 0xedb88320
// is reversed bits of normal representation 0x04c11db7

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t POLY = 0;

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
	uint32_t input = strtoul(av[1], NULL, 16);

	POLY = 0xedb88320;
	if(ac > 2)
		POLY = strtoul(av[2], NULL, 16);

	printf("crc32(%08X, POLY=%08X) == %08X\n", input, POLY, rc_crc32(0, (const char *)&input, sizeof(uint32_t)));
	return 0;
}
