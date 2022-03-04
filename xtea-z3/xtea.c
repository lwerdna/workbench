#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "xtea_tests.h"

/* implementation from https://en.wikipedia.org/wiki/XTEA
 * MODS:
 *   - rounds hardcoded to 32
 *   - add "out" parameter instead of encrypting in place
 */
void xtea_encipher(uint32_t plaintext[2], uint32_t const key[4], uint32_t ciphertext[2])
{
    unsigned int i;
    uint32_t v0 = plaintext[0], v1 = plaintext[1], sum = 0, delta = 0x9E3779B9;
    for (i=0; i < 32; i++)
    {
        //printf("\t// round %d\n", i);
        //printf("\tv0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x%08X + key[%d]);\n", sum, sum & 3);
        //printf("\tv0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x%08X;\n", sum + key[sum & 3]);
        v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (sum + key[sum & 3]);
        sum += delta;
        //printf("\tv1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x%08X + key[%d]);\n", sum, (sum >> 11) & 3);
        //printf("\tv1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x%08X;\n", sum + key[(sum>>11) & 3]);
        v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (sum + key[(sum>>11) & 3]);
    }
    ciphertext[0] = v0;
    ciphertext[1] = v1;
}

/* MODS:
 *   - loops unrolled
 *   - delta,sum (key schedule) precomputed
 */
void xtea_encipher_expanded(uint32_t plaintext[2], uint32_t const key[4], uint32_t ciphertext[2])
{
    uint32_t v0 = plaintext[0], v1 = plaintext[1];
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x00000000 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x9E3779B9 + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x9E3779B9 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x3C6EF372 + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x3C6EF372 + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xDAA66D2B + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xDAA66D2B + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x78DDE6E4 + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x78DDE6E4 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x1715609D + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x1715609D + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xB54CDA56 + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xB54CDA56 + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x5384540F + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x5384540F + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xF1BBCDC8 + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xF1BBCDC8 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x8FF34781 + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x8FF34781 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x2E2AC13A + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x2E2AC13A + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xCC623AF3 + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xCC623AF3 + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x6A99B4AC + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x6A99B4AC + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x08D12E65 + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x08D12E65 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xA708A81E + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xA708A81E + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x454021D7 + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x454021D7 + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xE3779B90 + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xE3779B90 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x81AF1549 + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x81AF1549 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x1FE68F02 + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x1FE68F02 + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xBE1E08BB + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xBE1E08BB + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x5C558274 + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x5C558274 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xFA8CFC2D + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xFA8CFC2D + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x98C475E6 + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x98C475E6 + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x36FBEF9F + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x36FBEF9F + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xD5336958 + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xD5336958 + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x736AE311 + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x736AE311 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x11A25CCA + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x11A25CCA + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xAFD9D683 + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xAFD9D683 + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x4E11503C + key[2]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x4E11503C + key[0]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xEC48C9F5 + key[1]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0xEC48C9F5 + key[1]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x8A8043AE + key[0]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x8A8043AE + key[2]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x28B7BD67 + key[3]);
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (0x28B7BD67 + key[3]);
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0xC6EF3720 + key[2]);
    ciphertext[0] = v0;
    ciphertext[1] = v1;
}

/* MODS:
 *   - hardcoded key: 0x00010203,0x04050607,0x08090A0B,0x0C0D0E0F
 */
void xtea_encipher_fixed_key(uint32_t plaintext[2], uint32_t ciphertext[2])
{
    uint32_t v0 = plaintext[0], v1 = plaintext[1];
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x00010203;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xAA4487C8;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xA23C7FC0;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x4477FD7D;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x4477FD7D;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xDEAB7332;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xE6B37B3A;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x78DEE8E7;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x78DEE8E7;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x171662A0;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x1B1A66A4;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xC159E865;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xBD55E461;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x5B8D5E1A;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x5F91621E;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xF5C0D3CF;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xF1BCCFCB;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x8FF44984;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x93F84D88;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x2E2BC33D;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x3633CB45;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xD86F4902;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xD86F4902;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x72A2BEB7;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x6A9AB6AF;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x0CD6346C;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x0CD6346C;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xAB0DAE25;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xAF11B229;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x454123DA;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x514D2FE6;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xEF84A99F;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xE3789D93;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x89B81F54;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x85B41B50;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x23EB9509;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x27EF990D;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xC2230EC2;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xCA2B16CA;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x5C568477;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x5C568477;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x069A0A3C;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xFE920234;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xA0CD7FF1;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xA0CD7FF1;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x3B00F5A6;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x4308FDAE;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xD9386F5F;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xD5346B5B;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x736BE514;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x776FE918;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x1DAF6AD9;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x19AB66D5;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xB7E2E08E;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xBBE6E492;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x561A5A47;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x4E12523F;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xF04DCFFC;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0xF04DCFFC;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x8A8145B1;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x92894DB9;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x34C4CB76;
	v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ 0x34C4CB76;
	v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0xCEF8412B;
    ciphertext[0] = v0;
    ciphertext[1] = v1;
}

void assert(bool condition)
{
	if(!condition)
	{
		printf("ASSERTION FAILED!\n");
		exit(-1);
	}
}

int main(int ac, char **av)
{
	/* test base implementation */
	test_suite(xtea_encipher);
	/* test unrolled+precomputed implementation */
	test_suite(xtea_encipher_expanded);

	/* test hardcoded key */
	uint32_t ptext[2] = {0x00112233,0x44556677};
	uint32_t ctext[2] = {0, 0};
	xtea_encipher_fixed_key(ptext, ctext);
	assert(ctext[0] == 0xd9a4f870);
	assert(ctext[1] == 0xba1f45d6);

	printf("PASS\n");
	return 0;
}
