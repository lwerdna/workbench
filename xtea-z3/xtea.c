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
        //printf("\tuint32_t a%d = a%d + ((((b%d << 4) ^ (b%d >> 5)) + b%d) ^ 0x%08X);\n", i+1, i, i, i, i, sum + key[sum & 3]);
        v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (sum + key[sum & 3]);
        sum += delta;
        //printf("\tv1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (0x%08X + key[%d]);\n", sum, (sum >> 11) & 3);
        //printf("\tv1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ 0x%08X;\n", sum + key[(sum>>11) & 3]);
        //printf("\tuint32_t b%d = b%d + ((((a%d << 4) ^ (a%d >> 5)) + a%d) ^ 0x%08X);\n", i+1, i, i+1, i+1, i+1, sum + key[(sum>>11) & 3]);
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

/* MODS:
 *   - hardcoded key: 0x00010203,0x04050607,0x08090A0B,0x0C0D0E0F
 *   - ssa
 */
void xtea_encipher_fixed_key_ssa(uint32_t plaintext[2], uint32_t ciphertext[2])
{
	uint32_t a0 = plaintext[0];
	uint32_t b0 = plaintext[1];
	uint32_t a1 = a0 + ((((b0 << 4) ^ (b0 >> 5)) + b0) ^ 0x00010203);
	uint32_t b1 = b0 + ((((a1 << 4) ^ (a1 >> 5)) + a1) ^ 0xAA4487C8);
	uint32_t a2 = a1 + ((((b1 << 4) ^ (b1 >> 5)) + b1) ^ 0xA23C7FC0);
	uint32_t b2 = b1 + ((((a2 << 4) ^ (a2 >> 5)) + a2) ^ 0x4477FD7D);
	uint32_t a3 = a2 + ((((b2 << 4) ^ (b2 >> 5)) + b2) ^ 0x4477FD7D);
	uint32_t b3 = b2 + ((((a3 << 4) ^ (a3 >> 5)) + a3) ^ 0xDEAB7332);
	uint32_t a4 = a3 + ((((b3 << 4) ^ (b3 >> 5)) + b3) ^ 0xE6B37B3A);
	uint32_t b4 = b3 + ((((a4 << 4) ^ (a4 >> 5)) + a4) ^ 0x78DEE8E7);
	uint32_t a5 = a4 + ((((b4 << 4) ^ (b4 >> 5)) + b4) ^ 0x78DEE8E7);
	uint32_t b5 = b4 + ((((a5 << 4) ^ (a5 >> 5)) + a5) ^ 0x171662A0);
	uint32_t a6 = a5 + ((((b5 << 4) ^ (b5 >> 5)) + b5) ^ 0x1B1A66A4);
	uint32_t b6 = b5 + ((((a6 << 4) ^ (a6 >> 5)) + a6) ^ 0xC159E865);
	uint32_t a7 = a6 + ((((b6 << 4) ^ (b6 >> 5)) + b6) ^ 0xBD55E461);
	uint32_t b7 = b6 + ((((a7 << 4) ^ (a7 >> 5)) + a7) ^ 0x5B8D5E1A);
	uint32_t a8 = a7 + ((((b7 << 4) ^ (b7 >> 5)) + b7) ^ 0x5F91621E);
	uint32_t b8 = b7 + ((((a8 << 4) ^ (a8 >> 5)) + a8) ^ 0xF5C0D3CF);
	uint32_t a9 = a8 + ((((b8 << 4) ^ (b8 >> 5)) + b8) ^ 0xF1BCCFCB);
	uint32_t b9 = b8 + ((((a9 << 4) ^ (a9 >> 5)) + a9) ^ 0x8FF44984);
	uint32_t a10 = a9 + ((((b9 << 4) ^ (b9 >> 5)) + b9) ^ 0x93F84D88);
	uint32_t b10 = b9 + ((((a10 << 4) ^ (a10 >> 5)) + a10) ^ 0x2E2BC33D);
	uint32_t a11 = a10 + ((((b10 << 4) ^ (b10 >> 5)) + b10) ^ 0x3633CB45);
	uint32_t b11 = b10 + ((((a11 << 4) ^ (a11 >> 5)) + a11) ^ 0xD86F4902);
	uint32_t a12 = a11 + ((((b11 << 4) ^ (b11 >> 5)) + b11) ^ 0xD86F4902);
	uint32_t b12 = b11 + ((((a12 << 4) ^ (a12 >> 5)) + a12) ^ 0x72A2BEB7);
	uint32_t a13 = a12 + ((((b12 << 4) ^ (b12 >> 5)) + b12) ^ 0x6A9AB6AF);
	uint32_t b13 = b12 + ((((a13 << 4) ^ (a13 >> 5)) + a13) ^ 0x0CD6346C);
	uint32_t a14 = a13 + ((((b13 << 4) ^ (b13 >> 5)) + b13) ^ 0x0CD6346C);
	uint32_t b14 = b13 + ((((a14 << 4) ^ (a14 >> 5)) + a14) ^ 0xAB0DAE25);
	uint32_t a15 = a14 + ((((b14 << 4) ^ (b14 >> 5)) + b14) ^ 0xAF11B229);
	uint32_t b15 = b14 + ((((a15 << 4) ^ (a15 >> 5)) + a15) ^ 0x454123DA);
	uint32_t a16 = a15 + ((((b15 << 4) ^ (b15 >> 5)) + b15) ^ 0x514D2FE6);
	uint32_t b16 = b15 + ((((a16 << 4) ^ (a16 >> 5)) + a16) ^ 0xEF84A99F);
	uint32_t a17 = a16 + ((((b16 << 4) ^ (b16 >> 5)) + b16) ^ 0xE3789D93);
	uint32_t b17 = b16 + ((((a17 << 4) ^ (a17 >> 5)) + a17) ^ 0x89B81F54);
	uint32_t a18 = a17 + ((((b17 << 4) ^ (b17 >> 5)) + b17) ^ 0x85B41B50);
	uint32_t b18 = b17 + ((((a18 << 4) ^ (a18 >> 5)) + a18) ^ 0x23EB9509);
	uint32_t a19 = a18 + ((((b18 << 4) ^ (b18 >> 5)) + b18) ^ 0x27EF990D);
	uint32_t b19 = b18 + ((((a19 << 4) ^ (a19 >> 5)) + a19) ^ 0xC2230EC2);
	uint32_t a20 = a19 + ((((b19 << 4) ^ (b19 >> 5)) + b19) ^ 0xCA2B16CA);
	uint32_t b20 = b19 + ((((a20 << 4) ^ (a20 >> 5)) + a20) ^ 0x5C568477);
	uint32_t a21 = a20 + ((((b20 << 4) ^ (b20 >> 5)) + b20) ^ 0x5C568477);
	uint32_t b21 = b20 + ((((a21 << 4) ^ (a21 >> 5)) + a21) ^ 0x069A0A3C);
	uint32_t a22 = a21 + ((((b21 << 4) ^ (b21 >> 5)) + b21) ^ 0xFE920234);
	uint32_t b22 = b21 + ((((a22 << 4) ^ (a22 >> 5)) + a22) ^ 0xA0CD7FF1);
	uint32_t a23 = a22 + ((((b22 << 4) ^ (b22 >> 5)) + b22) ^ 0xA0CD7FF1);
	uint32_t b23 = b22 + ((((a23 << 4) ^ (a23 >> 5)) + a23) ^ 0x3B00F5A6);
	uint32_t a24 = a23 + ((((b23 << 4) ^ (b23 >> 5)) + b23) ^ 0x4308FDAE);
	uint32_t b24 = b23 + ((((a24 << 4) ^ (a24 >> 5)) + a24) ^ 0xD9386F5F);
	uint32_t a25 = a24 + ((((b24 << 4) ^ (b24 >> 5)) + b24) ^ 0xD5346B5B);
	uint32_t b25 = b24 + ((((a25 << 4) ^ (a25 >> 5)) + a25) ^ 0x736BE514);
	uint32_t a26 = a25 + ((((b25 << 4) ^ (b25 >> 5)) + b25) ^ 0x776FE918);
	uint32_t b26 = b25 + ((((a26 << 4) ^ (a26 >> 5)) + a26) ^ 0x1DAF6AD9);
	uint32_t a27 = a26 + ((((b26 << 4) ^ (b26 >> 5)) + b26) ^ 0x19AB66D5);
	uint32_t b27 = b26 + ((((a27 << 4) ^ (a27 >> 5)) + a27) ^ 0xB7E2E08E);
	uint32_t a28 = a27 + ((((b27 << 4) ^ (b27 >> 5)) + b27) ^ 0xBBE6E492);
	uint32_t b28 = b27 + ((((a28 << 4) ^ (a28 >> 5)) + a28) ^ 0x561A5A47);
	uint32_t a29 = a28 + ((((b28 << 4) ^ (b28 >> 5)) + b28) ^ 0x4E12523F);
	uint32_t b29 = b28 + ((((a29 << 4) ^ (a29 >> 5)) + a29) ^ 0xF04DCFFC);
	uint32_t a30 = a29 + ((((b29 << 4) ^ (b29 >> 5)) + b29) ^ 0xF04DCFFC);
	uint32_t b30 = b29 + ((((a30 << 4) ^ (a30 >> 5)) + a30) ^ 0x8A8145B1);
	uint32_t a31 = a30 + ((((b30 << 4) ^ (b30 >> 5)) + b30) ^ 0x92894DB9);
	uint32_t b31 = b30 + ((((a31 << 4) ^ (a31 >> 5)) + a31) ^ 0x34C4CB76);
	uint32_t a32 = a31 + ((((b31 << 4) ^ (b31 >> 5)) + b31) ^ 0x34C4CB76);
	uint32_t b32 = b31 + ((((a32 << 4) ^ (a32 >> 5)) + a32) ^ 0xCEF8412B);
	ciphertext[0] = a32;
    ciphertext[1] = b32;
}

void assert(char *label, bool condition)
{
	if(!condition)
	{
		printf("ASSERTION \"%s\" FAILED!\n", label);
		exit(-1);
	}
}

int main(int ac, char **av)
{
	/* test hardcoded key */
	uint32_t ptext[2] = {0x00112233,0x44556677};
	uint32_t key[4] = {0x00010203,0x04050607,0x08090A0B,0x0C0D0E0F}; 
	uint32_t ctext[2] = {0, 0};

	//xtea_encipher(ptext, key, ctext);
	//exit(-1);

	xtea_encipher_fixed_key(ptext, ctext);
	assert("1", ctext[0] == 0xd9a4f870);
	assert("2", ctext[1] == 0xba1f45d6);

	xtea_encipher_fixed_key_ssa(ptext, ctext);
	assert("3", ctext[0] == 0xd9a4f870);
	assert("4", ctext[1] == 0xba1f45d6);

	/* test base implementation */
	test_suite(xtea_encipher);
	/* test unrolled+precomputed implementation */
	test_suite(xtea_encipher_expanded);

	printf("PASS\n");
	return 0;
}
